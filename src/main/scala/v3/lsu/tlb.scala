package boom.v3.lsu

import chisel3._
import chisel3.util._

import org.chipsalliance.cde.config.Parameters
import freechips.rocketchip.rocket._
import freechips.rocketchip.tilelink._
import freechips.rocketchip.subsystem.{CacheBlockBytes}
import freechips.rocketchip.diplomacy.{RegionType}
import freechips.rocketchip.util._

import boom.v3.common._
import boom.v3.exu.{BrResolutionInfo, Exception, FuncUnitResp, CommitSignals}
import boom.v3.util.{BoolToChar, AgePriorityEncoder, IsKilledByBranch, GetNewBrMask, WrapInc, IsOlder, UpdateBrMask}

class NBDTLB(instruction: Boolean, lgMaxSize: Int, cfg: TLBConfig)(implicit edge: TLEdgeOut, p: Parameters) extends BoomModule()(p) {
  require(!instruction)
  require(!boomParams.useNACC || !usingHypervisor, "NACC does not support hypervisor translation")
  require(!boomParams.useNACC || (xLen == 64 && pgLevels == 3 && pgLevelBits == 9 && pgIdxBits == 12),
    "NACC currently requires RV64 Sv39")
  val io = IO(new Bundle {
    val req = Flipped(Vec(memWidth, Decoupled(new TLBReq(lgMaxSize))))
    val naccPTW = boomParams.useNACC.option(Input(Vec(memWidth, Bool())))
    val miss_rdy = Output(Bool())
    val resp = Output(Vec(memWidth, new TLBResp))
    val sfence = Input(Valid(new SFenceReq))
    val ptw = new TLBPTWIO
    val kill = Input(Bool())
  })
  io.ptw := DontCare
  io.resp := DontCare

  class EntryData extends Bundle {
    val ppn = UInt(ppnBits.W)
    val u = Bool()
    val g = Bool()
    val ae = Bool()
    val sw = Bool()
    val sx = Bool()
    val sr = Bool()
    val pw = Bool()
    val px = Bool()
    val pr = Bool()
    val pal = Bool() // AMO logical
    val paa = Bool() // AMO arithmetic
    val eff = Bool() // get/put effects
    val c = Bool()
    val inNACCAgentRegion = boomParams.useNACC.option(Bool())
    val naccBitmapTag = boomParams.useNACC.option(UInt(NACCBitmapTag.Width.W))
    val fragmented_superpage = Bool()
  }

  class Entry(val nSectors: Int, val superpage: Boolean, val superpageOnly: Boolean) extends Bundle {
    require(nSectors == 1 || !superpage)
    require(isPow2(nSectors))
    require(!superpageOnly || superpage)

    val level = UInt(log2Ceil(pgLevels).W)
    val tag = UInt(vpnBits.W)
    val data = Vec(nSectors, UInt(new EntryData().getWidth.W))
    val valid = Vec(nSectors, Bool())
    def entry_data = data.map(_.asTypeOf(new EntryData))

    private def sectorIdx(vpn: UInt) = vpn.extract(log2Ceil(nSectors)-1, 0)
    def getData(vpn: UInt) = OptimizationBarrier(data(sectorIdx(vpn)).asTypeOf(new EntryData))
    def sectorHit(vpn: UInt) = valid.orR && sectorTagMatch(vpn)
    def sectorTagMatch(vpn: UInt) = ((tag ^ vpn) >> log2Ceil(nSectors)) === 0.U
    def hit(vpn: UInt) = {
      if (superpage && usingVM) {
        var tagMatch = valid.head
        for (j <- 0 until pgLevels) {
          val base = vpnBits - (j + 1) * pgLevelBits
          val ignore = level < j.U || (superpageOnly && j == pgLevels - 1).B
          tagMatch = tagMatch && (ignore || tag(base + pgLevelBits - 1, base) === vpn(base + pgLevelBits - 1, base))
        }
        tagMatch
      } else {
        val idx = sectorIdx(vpn)
        valid(idx) && sectorTagMatch(vpn)
      }
    }
    def ppn(vpn: UInt) = {
      val data = getData(vpn)
      if (superpage && usingVM) {
        var res = data.ppn >> pgLevelBits*(pgLevels - 1)
        for (j <- 1 until pgLevels) {
          val ignore = (level < j.U) || (superpageOnly && j == pgLevels - 1).B
          res = Cat(res, (Mux(ignore, vpn, 0.U) | data.ppn)(vpnBits - j*pgLevelBits - 1, vpnBits - (j + 1)*pgLevelBits))
        }
        res
      } else {
        data.ppn
      }
    }

    def insert(tag: UInt, level: UInt, entry: EntryData) {
      this.tag := tag
      this.level := level.extract(log2Ceil(pgLevels - superpageOnly.toInt)-1, 0)

      val idx = sectorIdx(tag)
      valid(idx) := true.B
      data(idx) := entry.asUInt
    }

    def invalidate() { valid.foreach(_ := false.B) }
    def invalidateVPN(vpn: UInt) {
      if (superpage) {
         when (hit(vpn)) { invalidate() }
      } else {
        when (sectorTagMatch(vpn)) { valid(sectorIdx(vpn)) := false.B }

        // For fragmented superpage mappings, we assume the worst (largest)
        // case, and zap entries whose most-significant VPNs match
         when (((tag ^ vpn) >> (pgLevelBits * (pgLevels - 1))) === 0.U) {
           for ((v, e) <- valid zip entry_data)
             when (e.fragmented_superpage) { v := false.B }
         }
      }
    }
    def invalidateNonGlobal() {
       for ((v, e) <- valid zip entry_data)
         when (!e.g) { v := false.B }
    }
  }

  def widthMap[T <: Data](f: Int => T) = VecInit((0 until memWidth).map(f))

  val pageGranularityPMPs = pmpGranularity >= (1 << pgIdxBits)
  val sectored_entries = Reg(Vec((cfg.nSets * cfg.nWays) / cfg.nSectors, new Entry(cfg.nSectors, false, false)))
  val superpage_entries = Reg(Vec(cfg.nSuperpageEntries, new Entry(1, true, true)))
  val special_entry = (!pageGranularityPMPs).option(Reg(new Entry(1, true, false)))
  def ordinary_entries = sectored_entries ++ superpage_entries
  def all_entries = ordinary_entries ++ special_entry

  val s_ready :: s_request :: s_wait :: s_wait_invalidate :: Nil = Enum(4)
  val state = RegInit(s_ready)
  val r_naccBitmapOnly = boomParams.useNACC.option(RegInit(false.B))
  val r_naccBitmapPPN = boomParams.useNACC.option(Reg(UInt(ppnBits.W)))
  val r_naccRootValidationOnly = boomParams.useNACC.option(RegInit(false.B))
  val r_naccPendingRequestEffectiveSU = boomParams.useNACC.option(Reg(Bool()))
  val r_naccBitmapResponseStale = boomParams.useNACC.option(RegInit(false.B))
  val naccBareTagValid = boomParams.useNACC.option(RegInit(false.B))
  val naccBareTagPPN = boomParams.useNACC.option(Reg(UInt(ppnBits.W)))
  val naccBareTag = boomParams.useNACC.option(Reg(UInt(NACCBitmapTag.Width.W)))
  val r_refill_tag = Reg(UInt(vpnBits.W))
  val r_superpage_repl_addr = Reg(UInt(log2Ceil(superpage_entries.size).W))
  val r_sectored_repl_addr = Reg(UInt(log2Ceil(sectored_entries.size).W))
  val r_sectored_hit_addr = Reg(UInt(log2Ceil(sectored_entries.size).W))
  val r_sectored_hit = Reg(Bool())

  val priv = if (instruction) io.ptw.status.prv else io.ptw.status.dprv
  val priv_s = priv(0)
  val priv_uses_vm = priv <= PRV.S.U
  val vm_enabled = widthMap(w => usingVM.B && io.ptw.ptbr.mode(io.ptw.ptbr.mode.getWidth-1) && priv_uses_vm && !io.req(w).bits.passthrough)
  val naccBitmapFatal = if (boomParams.useNACC) io.ptw.naccBitmapFatal.get else false.B
  val naccBitmapFatalApplies = widthMap(w =>
    naccBitmapFatal && priv_uses_vm && !io.req(w).bits.passthrough)

  // share a single physical memory attribute checker (unshare if critical path)
  val vpn = widthMap(w => io.req(w).bits.vaddr(vaddrBits-1, pgIdxBits))
  val refill_ppn = io.ptw.resp.bits.pte.ppn(ppnBits-1, 0)
  val naccBitmapOnlyResponse = if (boomParams.useNACC) {
    usingVM.B && io.ptw.resp.valid && io.ptw.resp.bits.naccBitmapOnly.get
  } else {
    false.B
  }
  val naccRootValidationOnlyResponse = if (boomParams.useNACC) {
    naccBitmapOnlyResponse && io.ptw.resp.bits.naccRootValidationOnly.get
  } else {
    false.B
  }
  val ptwTranslationResponse = usingVM.B && io.ptw.resp.valid && !naccBitmapOnlyResponse
  val do_refill = ptwTranslationResponse && !naccBitmapFatal
  val invalidate_refill = state.isOneOf(s_request /* don't care */, s_wait_invalidate) || io.sfence.valid
  val mpu_ppn = widthMap(w =>
                Mux(do_refill, refill_ppn,
                Mux(vm_enabled(w) && special_entry.nonEmpty.B, special_entry.map(_.ppn(vpn(w))).getOrElse(0.U), io.req(w).bits.vaddr >> pgIdxBits)))
  val mpu_physaddr = widthMap(w => Cat(mpu_ppn(w), io.req(w).bits.vaddr(pgIdxBits-1, 0)))
  def inNACCAgentRegion(addr: UInt): Bool = if (boomParams.useNACC) {
    val physicalAddress = addr.padTo(xLen)
    physicalAddress >= io.ptw.customCSRs.naccSagentValue &&
      physicalAddress < io.ptw.customCSRs.naccEagentValue
  } else {
    false.B
  }
  def inNACCBitmapTargetRange(addr: UInt): Bool = if (boomParams.useNACC) {
    val physicalAddress = addr.padTo(xLen)
    physicalAddress >= io.ptw.customCSRs.naccBitmapTargetStartValue &&
      physicalAddress < io.ptw.customCSRs.naccBitmapTargetEndValue
  } else {
    false.B
  }
  /** final PA 是否与 packed bitmap backing memory 相交。
    * backing 大小由 target range 的 4 KiB 页数和每页 2 bit tag 唯一确定。
    */
  def overlapsNACCBitmapStorage(finalPPN: UInt, w: Int): Bool = if (boomParams.useNACC) {
    val calcWidth = xLen + 1
    val targetStart = io.ptw.customCSRs.naccBitmapTargetStartValue.padTo(calcWidth)
    val targetEnd = io.ptw.customCSRs.naccBitmapTargetEndValue.padTo(calcWidth)
    val targetValid = targetEnd > targetStart &&
      !io.ptw.customCSRs.naccBitmapTargetStartValue(pgIdxBits - 1, 0).orR &&
      !io.ptw.customCSRs.naccBitmapTargetEndValue(pgIdxBits - 1, 0).orR
    val pageCount = (targetEnd - targetStart) >> pgIdxBits
    val bitmapBytes = (pageCount + 3.U) >> 2
    val storageStart = io.ptw.customCSRs.naccBitmapStorageBaseValue.padTo(calcWidth)
    val storageEnd = storageStart +& bitmapBytes
    val accessStart = Cat(finalPPN, io.req(w).bits.vaddr(pgIdxBits - 1, 0)).padTo(calcWidth + 1)
    val accessBytes = (1.U((calcWidth + 1).W) << io.req(w).bits.size)
    val accessEnd = accessStart +& accessBytes
    targetValid && storageEnd > storageStart &&
      accessStart < storageEnd.padTo(calcWidth + 2) && accessEnd > storageStart.padTo(calcWidth + 2)
  } else {
    false.B
  }
  /** 当前 data access 的 effective world（AS/AU，含 MPRV+MPA）。
    *
    * hidden `A` 只经内部 bundle 传递，软件不可读写。
    * 全文件只有这一个「在不在 agent」的判据——早期相位模型的两个谓词（一个只看 state
    * 字段，一个还要求 CID 非零并区分 pendingReturn）可以给出相反答案，`A` 把它们合成
    * 一个 bit，这类不一致随之消失。
    */
  val naccAgentMode = if (boomParams.useNACC) io.ptw.customCSRs.asStatusValue(NACCStatus.InternalDataA) else false.B
  val naccRootPageAddress = io.ptw.ptbr.ppn << pgIdxBits
  val naccRootInBitmapTarget = if (boomParams.useNACC) {
    inNACCBitmapTargetRange(naccRootPageAddress)
  } else {
    false.B
  }
  val naccRootTagKnown = if (boomParams.useNACC) {
    !naccRootInBitmapTarget || io.ptw.naccRootTagValid.get
  } else {
    true.B
  }
  val naccRootTag = if (boomParams.useNACC) {
    Mux(naccRootInBitmapTarget, io.ptw.naccRootTag.get, NACCBitmapTag.Normal.U)
  } else {
    NACCBitmapTag.Normal.U
  }
  /** top-root role gate。只约束「`A=1` 时根表必须是 `ROOT_L0`」这一个方向；
    * 反方向（`A=0` 不许装 `ROOT_L0`）与「世界切换不改 `satp`」冲突，已删除。
    * 详见 rocket 侧 `TLB.scala` 中同名信号的说明。 */
  val naccRootAllowed = if (boomParams.useNACC) {
    !naccAgentMode ||
      (io.ptw.ptbr.mode(io.ptw.ptbr.mode.getWidth - 1) && naccRootInBitmapTarget &&
        naccRootTagKnown && naccRootTag === NACCBitmapTag.RootL0.U)
  } else {
    true.B
  }
  val naccEntryPrivilegeAllowed = priv === PRV.M.U || (priv === PRV.S.U && naccAgentMode)
  def naccBitmapTagAllowsRead(tag: UInt): Bool = {
    MuxLookup(tag, false.B)(Seq(
      NACCBitmapTag.Normal.U -> true.B,
      NACCBitmapTag.RootL0.U -> true.B,
      NACCBitmapTag.PrivateData.U -> (priv === PRV.M.U || naccAgentMode),
      NACCBitmapTag.PrivateCopyPending.U ->
        (priv === PRV.M.U || (naccAgentMode && priv === PRV.S.U))))
  }
  def naccBitmapTagAllowsWrite(tag: UInt): Bool = naccBitmapTagAllowsRead(tag)
  def naccBitmapTagAllowsExecute(tag: UInt): Bool = {
    MuxLookup(tag, false.B)(Seq(
      NACCBitmapTag.Normal.U -> true.B,
      NACCBitmapTag.RootL0.U -> (priv === PRV.M.U),
      NACCBitmapTag.PrivateData.U -> (priv === PRV.M.U || naccAgentMode),
      NACCBitmapTag.PrivateCopyPending.U -> (priv === PRV.M.U)))
  }
  // Bare最终physical PFN与TLBResp.paddr使用同一截断宽度，不能携带virtual高位。
  val naccBarePPN = widthMap(w => mpu_ppn(w)(ppnBits-1, 0))
  val naccBarePageAddress = widthMap(w => naccBarePPN(w) << pgIdxBits)
  val naccBareBitmapLookupRequired = widthMap(w => if (boomParams.useNACC) {
    priv_uses_vm && !io.ptw.ptbr.mode(io.ptw.ptbr.mode.getWidth-1) && !io.req(w).bits.passthrough &&
      inNACCBitmapTargetRange(naccBarePageAddress(w)) && !inNACCAgentRegion(naccBarePageAddress(w))
  } else {
    false.B
  })
  val naccBareTagHit = widthMap(w => if (boomParams.useNACC) {
    naccBareTagValid.get && naccBareTagPPN.get === naccBarePPN(w)
  } else {
    false.B
  })
  val naccBareBitmapMiss = widthMap(w =>
    naccBareBitmapLookupRequired(w) && !naccBareTagHit(w) && !naccBitmapFatalApplies(w))
  val naccPhysicalPrivilegeAllowed = widthMap(w => {
    val requestPrivilege = if (boomParams.useNACC) Mux(io.req(w).bits.passthrough, io.req(w).bits.prv, priv) else priv
    requestPrivilege === PRV.M.U || (requestPrivilege === PRV.S.U && naccAgentMode)
  })
  val pmp = Seq.fill(memWidth) { Module(new PMPChecker(lgMaxSize)) }
  for (w <- 0 until memWidth) {
    pmp(w).io.addr := mpu_physaddr(w)
    pmp(w).io.size := io.req(w).bits.size
    pmp(w).io.pmp := (io.ptw.pmp: Seq[PMP])
    pmp(w).io.prv := (if (boomParams.useNACC) {
      // Refill仍是S-effective；physical HellaCache request必须保留其真实dprv。
      Mux(usingVM.B && do_refill, PRV.S.U, Mux(io.req(w).bits.passthrough, io.req(w).bits.prv, priv))
    } else {
      Mux(usingVM.B && (do_refill || io.req(w).bits.passthrough /* PTW */), PRV.S.U, priv)
    })
  }
  val legal_address = widthMap(w => edge.manager.findSafe(mpu_physaddr(w)).reduce(_||_))
  def fastCheck(member: TLManagerParameters => Boolean, w: Int) =
    legal_address(w) && edge.manager.fastProperty(mpu_physaddr(w), member, (b:Boolean) => b.B)
  val cacheable = widthMap(w => fastCheck(_.supportsAcquireT, w) && (instruction || !usingDataScratchpad).B)
  val homogeneous = widthMap(w => TLBPageLookup(edge.manager.managers, xLen, p(CacheBlockBytes), BigInt(1) << pgIdxBits, 1 << lgMaxSize)(mpu_physaddr(w)).homogeneous)
  val prot_r   = widthMap(w => fastCheck(_.supportsGet, w) && pmp(w).io.r)
  val prot_w   = widthMap(w => fastCheck(_.supportsPutFull, w) && pmp(w).io.w)
  val prot_al  = widthMap(w => fastCheck(_.supportsLogical, w))
  val prot_aa  = widthMap(w => fastCheck(_.supportsArithmetic, w))
  val prot_x   = widthMap(w => fastCheck(_.executable, w) && pmp(w).io.x)
  val prot_eff = widthMap(w => fastCheck(Seq(RegionType.PUT_EFFECTS, RegionType.GET_EFFECTS) contains _.regionType, w))

  val sector_hits = widthMap(w => VecInit(sectored_entries.map(_.sectorHit(vpn(w)))))
  val superpage_hits = widthMap(w => VecInit(superpage_entries.map(_.hit(vpn(w)))))
  val hitsVec = widthMap(w => VecInit(all_entries.map(vm_enabled(w) && _.hit(vpn(w)))))
  val real_hits = widthMap(w => hitsVec(w).asUInt)
  val hits = widthMap(w => Cat(!vm_enabled(w), real_hits(w)))
  val ppn = widthMap(w => Mux1H(hitsVec(w) :+ !vm_enabled(w), all_entries.map(_.ppn(vpn(w))) :+ vpn(w)(ppnBits-1, 0)))

    // permission bit arrays
  when (do_refill) {
    val pte = io.ptw.resp.bits.pte
    val newEntry = Wire(new EntryData)
    newEntry.ppn := pte.ppn
    newEntry.c := cacheable(0)
    newEntry.u := pte.u
    newEntry.g := pte.g
    newEntry.ae := io.ptw.resp.bits.ae_final
    newEntry.sr := pte.sr()
    newEntry.sw := pte.sw()
    newEntry.sx := pte.sx()
    newEntry.pr := prot_r(0)
    newEntry.pw := prot_w(0)
    newEntry.px := prot_x(0)
    newEntry.pal := prot_al(0)
    newEntry.paa := prot_aa(0)
    newEntry.eff := prot_eff(0)
    newEntry.inNACCAgentRegion.foreach(_ := inNACCAgentRegion(refill_ppn << pgIdxBits))
    newEntry.naccBitmapTag.foreach(_ := io.ptw.resp.bits.naccBitmapTag.get)
    newEntry.fragmented_superpage := io.ptw.resp.bits.fragmented_superpage

    when (special_entry.nonEmpty.B && !io.ptw.resp.bits.homogeneous) {
      special_entry.foreach { e =>
        e.insert(r_refill_tag, io.ptw.resp.bits.level, newEntry)
        if (boomParams.useNACC) when (invalidate_refill) { e.invalidate() }
      }
    }.elsewhen (io.ptw.resp.bits.level < (pgLevels-1).U) {
      for ((e, i) <- superpage_entries.zipWithIndex) when (r_superpage_repl_addr === i.U) {
        e.insert(r_refill_tag, io.ptw.resp.bits.level, newEntry)
        if (boomParams.useNACC) when (invalidate_refill) { e.invalidate() }
      }
    }.otherwise {
      val waddr = Mux(r_sectored_hit, r_sectored_hit_addr, r_sectored_repl_addr)
      for ((e, i) <- sectored_entries.zipWithIndex) when (waddr === i.U) {
        when (!r_sectored_hit) { e.invalidate() }
        e.insert(r_refill_tag, 0.U, newEntry)
        if (boomParams.useNACC) when (invalidate_refill) { e.invalidate() }
      }
    }
  }

  val entries = widthMap(w => VecInit(all_entries.map(_.getData(vpn(w)))))
  val normal_entries = widthMap(w => VecInit(ordinary_entries.map(_.getData(vpn(w)))))
  val nPhysicalEntries = 1 + special_entry.size
  val ptw_ae_array = widthMap(w => Cat(false.B, entries(w).map(_.ae).asUInt))
  val priv_rw_ok   = widthMap(w => Mux(!priv_s || io.ptw.status.sum, entries(w).map(_.u).asUInt, 0.U) | Mux(priv_s, ~entries(w).map(_.u).asUInt, 0.U))
  val priv_x_ok    = widthMap(w => Mux(priv_s, ~entries(w).map(_.u).asUInt, entries(w).map(_.u).asUInt))
  val r_array      = widthMap(w => Cat(true.B, priv_rw_ok(w) & (entries(w).map(_.sr).asUInt | Mux(io.ptw.status.mxr, entries(w).map(_.sx).asUInt, 0.U))))
  val w_array      = widthMap(w => Cat(true.B, priv_rw_ok(w) & entries(w).map(_.sw).asUInt))
  val x_array      = widthMap(w => Cat(true.B, priv_x_ok(w)  & entries(w).map(_.sx).asUInt))
  val nacc_access_array = widthMap(w => if (boomParams.useNACC) {
    // 仅可信 PTW 内部请求绕过 ordinary Agent/backing gate；PMP/PMA 仍在 prot_* 合取。
    // 来源由 tile 仲裁器传入，不从当前 A 或 passthrough 单独推断。
    val ptwAccess = io.naccPTW.get(w) && io.req(w).bits.passthrough
    when (io.req(w).valid && io.naccPTW.get(w)) {
      assert(io.req(w).bits.passthrough, "NACC PTW request must use a physical address")
    }
    val physicalAccessAllowed = ptwAccess || (
      (!inNACCAgentRegion(mpu_physaddr(w)) || naccPhysicalPrivilegeAllowed(w)) &&
      (!overlapsNACCBitmapStorage(mpu_ppn(w), w) || naccPhysicalPrivilegeAllowed(w)))
    val entryAccessAllowed = (normal_entries(w).zip(ordinary_entries)).map { case (entry, tlbEntry) =>
      (!entry.inNACCAgentRegion.get || naccEntryPrivilegeAllowed) &&
        (!overlapsNACCBitmapStorage(tlbEntry.ppn(vpn(w)), w) || naccEntryPrivilegeAllowed)
    }
    Cat(Fill(nPhysicalEntries, physicalAccessAllowed), entryAccessAllowed.asUInt)
  } else {
    Fill(nPhysicalEntries + normal_entries(w).size, true.B)
  })
  /** `ROOT_L0` 页的读权限：只有**当前装着的那张**根页表可以被 S/U 读，其余
    * `ROOT_L0` 页（别的容器的根表）一律拒绝。
    *
    * AS 是系统级 trusted monitor，可读任意 `ROOT_L0`；其他 S/U/AU 只可读 live root。
    */
  val naccRootReadArray = widthMap(w => if (boomParams.useNACC) {
    def allowed(tag: UInt, finalPPN: UInt): Bool = {
      priv === PRV.M.U || tag =/= NACCBitmapTag.RootL0.U ||
        (naccAgentMode && priv === PRV.S.U) ||
        (io.ptw.ptbr.mode(io.ptw.ptbr.mode.getWidth - 1) && finalPPN === io.ptw.ptbr.ppn)
    }
    val physicalTag = Mux(naccBareBitmapLookupRequired(w), naccBareTag.get, NACCBitmapTag.Normal.U)
    val physicalAllowed = !naccBareBitmapLookupRequired(w) ||
      !naccBareTagHit(w) || allowed(physicalTag, naccBarePPN(w))
    val entryAllowed = (entries(w).zip(all_entries)).map { case (entry, tlbEntry) =>
      allowed(entry.naccBitmapTag.get, tlbEntry.ppn(vpn(w)))
    }
    Cat(physicalAllowed, entryAllowed.asUInt)
  } else {
    Fill(nPhysicalEntries + normal_entries(w).size, true.B)
  })
  val naccRootWriteArray = widthMap(w => if (boomParams.useNACC) {
    val offsetWidth = pgIdxBits + 1
    val accessStart = io.req(w).bits.vaddr(pgIdxBits - 1, 0).padTo(offsetWidth)
    val accessBytes = (1.U(offsetWidth.W) << io.req(w).bits.size)(offsetWidth - 1, 0)
    val accessEnd = accessStart +& accessBytes
    val entirelyInKernelHalf = accessStart >= (BigInt(1) << (pgIdxBits - 1)).U &&
      accessEnd <= (BigInt(1) << pgIdxBits).U
    // **这条是用户半保护的落点。** S 只能写当前装着的那张根页表，且访问 span 必须
    // 完整落在内核半 `[0x800,0x1000)`——于是不可信的 Linux 改不了 entry 0..255，
    // 无法重映射 agent 的地址空间，§「两类攻击」的共同前提就此消失。
    //
    // Linux S 只维护live root内核半；AS可管理整张以及非当前root。
    def allowed(tag: UInt, finalPPN: UInt): Bool = {
      priv === PRV.M.U || tag =/= NACCBitmapTag.RootL0.U ||
        (naccAgentMode && priv === PRV.S.U) ||
        (!naccAgentMode && priv === PRV.S.U &&
          io.ptw.ptbr.mode(io.ptw.ptbr.mode.getWidth - 1) && finalPPN === io.ptw.ptbr.ppn &&
          entirelyInKernelHalf)
    }
    val physicalTag = Mux(naccBareBitmapLookupRequired(w), naccBareTag.get, NACCBitmapTag.Normal.U)
    val physicalAllowed = !naccBareBitmapLookupRequired(w) ||
      !naccBareTagHit(w) || allowed(physicalTag, naccBarePPN(w))
    val entryAllowed = (entries(w).zip(all_entries)).map { case (entry, tlbEntry) =>
      allowed(entry.naccBitmapTag.get, tlbEntry.ppn(vpn(w)))
    }
    Cat(physicalAllowed, entryAllowed.asUInt)
  } else {
    Fill(nPhysicalEntries + normal_entries(w).size, true.B)
  })
  val naccTagReadArray = widthMap(w => if (boomParams.useNACC) {
    val physicalTag = Mux(naccBareBitmapLookupRequired(w), naccBareTag.get, NACCBitmapTag.Normal.U)
    val physicalAllowed = !naccBareBitmapLookupRequired(w) || !naccBareTagHit(w) ||
      naccBitmapTagAllowsRead(physicalTag)
    Cat(physicalAllowed, entries(w).map(e => naccBitmapTagAllowsRead(e.naccBitmapTag.get)).asUInt)
  } else Fill(nPhysicalEntries + normal_entries(w).size, true.B))
  val naccTagWriteArray = widthMap(w => if (boomParams.useNACC) {
    val physicalTag = Mux(naccBareBitmapLookupRequired(w), naccBareTag.get, NACCBitmapTag.Normal.U)
    val physicalAllowed = !naccBareBitmapLookupRequired(w) || !naccBareTagHit(w) ||
      naccBitmapTagAllowsWrite(physicalTag)
    Cat(physicalAllowed, entries(w).map(e => naccBitmapTagAllowsWrite(e.naccBitmapTag.get)).asUInt)
  } else Fill(nPhysicalEntries + normal_entries(w).size, true.B))
  val naccTagExecuteArray = widthMap(w => if (boomParams.useNACC) {
    val physicalTag = Mux(naccBareBitmapLookupRequired(w), naccBareTag.get, NACCBitmapTag.Normal.U)
    val physicalAllowed = !naccBareBitmapLookupRequired(w) || !naccBareTagHit(w) ||
      naccBitmapTagAllowsExecute(physicalTag)
    Cat(physicalAllowed, entries(w).map(e => naccBitmapTagAllowsExecute(e.naccBitmapTag.get)).asUInt)
  } else Fill(nPhysicalEntries + normal_entries(w).size, true.B))
  val pr_array     = widthMap(w => Cat(Fill(nPhysicalEntries, prot_r(w))   , normal_entries(w).map(_.pr).asUInt) & ~ptw_ae_array(w) & nacc_access_array(w) & naccRootReadArray(w) & naccTagReadArray(w))
  val pw_array     = widthMap(w => Cat(Fill(nPhysicalEntries, prot_w(w))   , normal_entries(w).map(_.pw).asUInt) & ~ptw_ae_array(w) & nacc_access_array(w) & naccRootWriteArray(w) & naccTagWriteArray(w))
  val px_array     = widthMap(w => Cat(Fill(nPhysicalEntries, prot_x(w))   , normal_entries(w).map(_.px).asUInt) & ~ptw_ae_array(w) & nacc_access_array(w) & naccTagExecuteArray(w))
  val eff_array    = widthMap(w => Cat(Fill(nPhysicalEntries, prot_eff(w)) , normal_entries(w).map(_.eff).asUInt))
  val c_array      = widthMap(w => Cat(Fill(nPhysicalEntries, cacheable(w)), normal_entries(w).map(_.c).asUInt))
  val paa_array    = widthMap(w => Cat(Fill(nPhysicalEntries, prot_aa(w))  , normal_entries(w).map(_.paa).asUInt))
  val pal_array    = widthMap(w => Cat(Fill(nPhysicalEntries, prot_al(w))  , normal_entries(w).map(_.pal).asUInt))
  val paa_array_if_cached = widthMap(w => paa_array(w) | Mux(usingAtomicsInCache.B, c_array(w), 0.U))
  val pal_array_if_cached = widthMap(w => pal_array(w) | Mux(usingAtomicsInCache.B, c_array(w), 0.U))
  val prefetchable_array  = widthMap(w => Cat((cacheable(w) && homogeneous(w)) << (nPhysicalEntries-1), normal_entries(w).map(_.c).asUInt))

  val misaligned = widthMap(w => (io.req(w).bits.vaddr & (UIntToOH(io.req(w).bits.size) - 1.U)).orR)
  val bad_va = widthMap(w => if (!usingVM || (minPgLevels == pgLevels && vaddrBits == vaddrBitsExtended)) false.B else vm_enabled(w) && {
    val nPgLevelChoices = pgLevels - minPgLevels + 1
    val minVAddrBits = pgIdxBits + minPgLevels * pgLevelBits
    (for (i <- 0 until nPgLevelChoices) yield {
      val mask = ((BigInt(1) << vaddrBitsExtended) - (BigInt(1) << (minVAddrBits + i * pgLevelBits - 1))).U
      val maskedVAddr = io.req(w).bits.vaddr & mask
      io.ptw.ptbr.additionalPgLevels === i.U && !(maskedVAddr === 0.U || maskedVAddr === mask)
    }).orR
  })
  // 与 rocket 侧一致：root tag 只有 `A=1` 时被 `naccRootAllowed` 消费，故只在那时才取。
  val naccRootValidationMiss = widthMap(w => boomParams.useNACC.B && vm_enabled(w) && !bad_va(w) &&
    naccAgentMode && naccRootInBitmapTarget && !naccRootTagKnown && !naccBitmapFatalApplies(w))
  /** `A=1` 但 stage-1 分页未启用（`satp.MODE = Bare`）时一律拒绝。
    *
    * **为什么必须与 root role gate 并列，而不能塞进它的 `vm_enabled` 前提里**：
    * `vm_enabled = usingVM && ptbr.MODE != Bare && priv_uses_vm && !passthrough`。
    * `satp.MODE = Bare` 时 `vm_enabled` 为假，下面 `naccRootDenied` 的第一个
    * disjunct 恒为假——**root gate 整个不评估**。也就是说，只要先把 `satp` 切回
    * Bare 再进 A 世界，「根表必须是 `ROOT_L0`」这条检查就被完整绕开了。所以这个
    * disjunct 必须自带前提、独立成立。
    *
    * **为什么 Bare 下只能拒绝**：`A=1` 必须跑在 monitor 认可过的根页表上，这是
    * 整个模型的安全地基。不分页时根本没有根页表可查，不可信的 S-mode 软件不需要
    * 伪造任何 PTE，agent 看到的整个地址空间就直接等于物理地址空间、完全由它决定；
    * 连带地，Agent region 的准入判据把「`A=1` 的 S-mode」视为可信，于是 Agent
    * region 也一并敞开。这里不存在「先放行、事后补检查」的中间状态，唯一正确的
    * 答案是拒绝。
    *
    * 各个前提分别挡住谁：
    *   - `naccAgentMode`：`A=0` 时本条恒为假、零影响。普通 Linux 在早期 boot 用
    *     `satp = Bare` 跑是完全合法的，绝不能因此 fault。
    *   - `priv_uses_vm`：M-effective 的访问本来就不经 stage-1 翻译，不受本条约束。
    *   - `!passthrough`：physical HellaCache request / PTW 自身访问不受本条约束。
    *   - `!naccBitmapFatalApplies(w)`：与另一个 disjunct 一致，sticky fatal 优先。
    * 不必重复 `!bad_va(w)`：`bad_va` 蕴含 `vm_enabled`，本条成立时它必为假。
    */
  // `usingVM.B &&` 是为了与 rocket 侧对齐：那边用的 `stage1_en` 本身含 `usingVM.B`，
  // 于是 useNACC 且 usingVM=false 这个退化配置下两侧同为 fail-closed（没有 VM 就没有
  // satp，「A=1 时 satp.PPN 必须是 ROOT_L0 页」这条不变量不可能满足）。NACC 一律用
  // Sv39，实际碰不到这个组合，但拒绝的方向必须两侧一致，不能各随各的局部写法。
  val naccRootStage1Missing = widthMap(w => boomParams.useNACC.B && naccAgentMode &&
    priv_uses_vm && !(usingVM.B && io.ptw.ptbr.mode(io.ptw.ptbr.mode.getWidth-1)) &&
    !io.req(w).bits.passthrough && !naccBitmapFatalApplies(w))
  /** root gate 的总拒绝信号。两个 disjunct 走同一条汇合路径：抑制同周期的
    * page fault 与 miss，改为产出 access fault。 */
  val naccRootDenied = widthMap(w => (boomParams.useNACC.B && vm_enabled(w) && !bad_va(w) &&
    !naccRootValidationMiss(w) && !naccRootAllowed && !naccBitmapFatalApplies(w)) ||
    naccRootStage1Missing(w))
  /** AU只能使用Sv39用户半；AS仍可按普通权限访问Linux高半NORMAL映射。 */
  val naccAUHighHalfDenied = widthMap(w => boomParams.useNACC.B && naccAgentMode &&
    priv === PRV.U.U && io.req(w).bits.vaddr(vaddrBits - 1) && !io.req(w).bits.passthrough)
  val naccAccessPolicyDenied = widthMap(w => naccRootDenied(w) || naccAUHighHalfDenied(w))

  val cmd_lrsc           = widthMap(w => usingAtomics.B && io.req(w).bits.cmd.isOneOf(M_XLR, M_XSC))
  val cmd_amo_logical    = widthMap(w => usingAtomics.B && isAMOLogical(io.req(w).bits.cmd))
  val cmd_amo_arithmetic = widthMap(w => usingAtomics.B && isAMOArithmetic(io.req(w).bits.cmd))
  val cmd_read           = widthMap(w => isRead(io.req(w).bits.cmd))
  val cmd_write          = widthMap(w => isWrite(io.req(w).bits.cmd))
  val cmd_write_perms    = widthMap(w => cmd_write(w) ||
    coreParams.haveCFlush.B && io.req(w).bits.cmd === M_FLUSH_ALL) // not a write, but needs write permissions
  val naccRootReadDenied = widthMap(w => boomParams.useNACC.B && !bad_va(w) && cmd_read(w) &&
    ((~naccRootReadArray(w)) & hits(w)).orR)
  val naccRootWriteDenied = widthMap(w => boomParams.useNACC.B && !bad_va(w) && cmd_write_perms(w) &&
    ((~naccRootWriteArray(w)) & hits(w)).orR)
  val naccTagReadDenied = widthMap(w => boomParams.useNACC.B && !bad_va(w) && cmd_read(w) &&
    ((~naccTagReadArray(w)) & hits(w)).orR)
  val naccTagWriteDenied = widthMap(w => boomParams.useNACC.B && !bad_va(w) && cmd_write_perms(w) &&
    ((~naccTagWriteArray(w)) & hits(w)).orR)
  val naccTagExecuteDenied = widthMap(w => boomParams.useNACC.B && instruction.B && !bad_va(w) &&
    ((~naccTagExecuteArray(w)) & hits(w)).orR)
  val naccTagPolicyDenied = widthMap(w => naccRootReadDenied(w) || naccRootWriteDenied(w) ||
    naccTagReadDenied(w) || naccTagWriteDenied(w) || naccTagExecuteDenied(w))

  val lrscAllowed = widthMap(w => Mux((usingDataScratchpad || usingAtomicsOnlyForIO).B, 0.U, c_array(w)))
  val ae_array = widthMap(w =>
    Mux(misaligned(w), eff_array(w), 0.U) |
    Mux(cmd_lrsc(w)  , ~lrscAllowed(w), 0.U))
  val ae_valid_array = widthMap(w => Cat(if (special_entry.isEmpty) true.B else Cat(true.B, Fill(special_entry.size, !do_refill)),
                                         Fill(normal_entries(w).size, true.B)))
  val ae_ld_array = widthMap(w => Mux(cmd_read(w), ae_array(w) | ~pr_array(w), 0.U))
  val ae_st_array = widthMap(w =>
    Mux(cmd_write_perms(w)   , ae_array(w) | ~pw_array(w), 0.U) |
    Mux(cmd_amo_logical(w)   , ~pal_array_if_cached(w), 0.U) |
    Mux(cmd_amo_arithmetic(w), ~paa_array_if_cached(w), 0.U))
  val must_alloc_array = widthMap(w =>
    Mux(cmd_amo_logical(w)   , ~paa_array(w), 0.U) |
    Mux(cmd_amo_arithmetic(w), ~pal_array(w), 0.U) |
    Mux(cmd_lrsc(w)          , ~0.U(pal_array(w).getWidth.W), 0.U))
  val ma_ld_array = widthMap(w => Mux(misaligned(w) && cmd_read(w) , ~eff_array(w), 0.U))
  val ma_st_array = widthMap(w => Mux(misaligned(w) && cmd_write(w), ~eff_array(w), 0.U))
  val pf_ld_array = widthMap(w => Mux(cmd_read(w)       , ~(r_array(w) | ptw_ae_array(w)), 0.U))
  val pf_st_array = widthMap(w => Mux(cmd_write_perms(w), ~(w_array(w) | ptw_ae_array(w)), 0.U))
  val pf_inst_array = widthMap(w => ~(x_array(w) | ptw_ae_array(w)))

  val tlb_hit = widthMap(w => real_hits(w).orR)
  val tlb_miss = widthMap(w =>
    vm_enabled(w) && !bad_va(w) && !tlb_hit(w) && !naccBitmapFatalApplies(w) &&
      !naccRootValidationMiss(w) && !naccAccessPolicyDenied(w))

  val sectored_plru = new PseudoLRU(sectored_entries.size)
  val superpage_plru = new PseudoLRU(superpage_entries.size)
  for (w <- 0 until memWidth) {
    when (io.req(w).valid && vm_enabled(w)) {
      when (sector_hits(w).orR) { sectored_plru.access(OHToUInt(sector_hits(w))) }
      when (superpage_hits(w).orR) { superpage_plru.access(OHToUInt(superpage_hits(w))) }
    }
  }

  // Superpages create the possibility that two entries in the TLB may match.
  // This corresponds to a software bug, but we can't return complete garbage;
  // we must return either the old translation or the new translation.  This
  // isn't compatible with the Mux1H approach.  So, flush the TLB and report
  // a miss on duplicate entries.
  val multipleHits = widthMap(w => PopCountAtLeast(real_hits(w), 2))

  io.miss_rdy := state === s_ready
  for (w <- 0 until memWidth) {
    io.req(w).ready    := true.B
    io.resp(w).pf.ld   := !naccBitmapFatalApplies(w) && !naccAccessPolicyDenied(w) && !naccTagPolicyDenied(w) && ((bad_va(w) && cmd_read(w)) || (pf_ld_array(w) & hits(w)).orR)
    io.resp(w).pf.st   := !naccBitmapFatalApplies(w) && !naccAccessPolicyDenied(w) && !naccTagPolicyDenied(w) && ((bad_va(w) && cmd_write_perms(w)) || (pf_st_array(w) & hits(w)).orR)
    io.resp(w).pf.inst := !naccBitmapFatalApplies(w) && !naccAccessPolicyDenied(w) && !naccTagPolicyDenied(w) && (bad_va(w) || (pf_inst_array(w) & hits(w)).orR)
    io.resp(w).ae.ld   := Mux(naccBitmapFatalApplies(w) || naccAccessPolicyDenied(w) || naccTagPolicyDenied(w), cmd_read(w), (ae_valid_array(w) & ae_ld_array(w) & hits(w)).orR)
    io.resp(w).ae.st   := Mux(naccBitmapFatalApplies(w) || naccAccessPolicyDenied(w) || naccTagPolicyDenied(w), cmd_write_perms(w), (ae_valid_array(w) & ae_st_array(w) & hits(w)).orR)
    io.resp(w).ae.inst := Mux(naccBitmapFatalApplies(w) || naccAccessPolicyDenied(w) || naccTagPolicyDenied(w), instruction.B, (ae_valid_array(w) & ~px_array(w) & hits(w)).orR)
    io.resp(w).ma.ld   := !naccBitmapFatalApplies(w) && !naccAccessPolicyDenied(w) && !naccTagPolicyDenied(w) && (ma_ld_array(w) & hits(w)).orR
    io.resp(w).ma.st   := !naccBitmapFatalApplies(w) && !naccAccessPolicyDenied(w) && !naccTagPolicyDenied(w) && (ma_st_array(w) & hits(w)).orR
    io.resp(w).ma.inst := false.B // this is up to the pipeline to figure out
    io.resp(w).cacheable    := (c_array(w) & hits(w)).orR
    io.resp(w).must_alloc   := (must_alloc_array(w) & hits(w)).orR
    io.resp(w).prefetchable := (prefetchable_array(w) & hits(w)).orR && edge.manager.managers.forall(m => !m.supportsAcquireB || m.supportsHint).B
    io.resp(w).miss  := Mux(naccBitmapFatalApplies(w) || naccAccessPolicyDenied(w) || naccTagPolicyDenied(w), false.B,
      ptwTranslationResponse || naccBitmapOnlyResponse || tlb_miss(w) || naccBareBitmapMiss(w) ||
        naccRootValidationMiss(w) || multipleHits(w))
    io.resp(w).paddr := Cat(ppn(w), io.req(w).bits.vaddr(pgIdxBits-1, 0))
    io.resp(w).size := io.req(w).bits.size
    io.resp(w).cmd := io.req(w).bits.cmd
  }

  val naccPendingPTWBlocked = if (boomParams.useNACC) {
    state === s_request && r_naccPendingRequestEffectiveSU.get && naccBitmapFatal
  } else {
    false.B
  }
  io.ptw.req.valid := state === s_request && !naccPendingPTWBlocked
  io.ptw.req.bits.valid := !io.kill
  io.ptw.req.bits.bits.addr := r_refill_tag
  io.ptw.req.bits.bits.naccBitmapOnly.foreach(_ := r_naccBitmapOnly.getOrElse(false.B))
  io.ptw.req.bits.bits.naccBitmapPPN.foreach(_ := r_naccBitmapPPN.getOrElse(0.U))
  io.ptw.req.bits.bits.naccRootValidationOnly.foreach(_ := r_naccRootValidationOnly.getOrElse(false.B))
  if (boomParams.useNACC) {
    // 当前NACC只支持no-hypervisor；bitmap-only请求必须显式关闭两阶段translation字段。
    io.ptw.req.bits.bits.need_gpa := false.B
    io.ptw.req.bits.bits.vstage1 := false.B
    io.ptw.req.bits.bits.stage2 := false.B
  }

  if (usingVM) {
    val sfence = io.sfence.valid
    if (boomParams.useNACC) {
      when (io.ptw.req.fire && io.ptw.req.bits.valid && r_naccBitmapOnly.get) {
        r_naccBitmapResponseStale.get := false.B
      }
      when ((sfence || io.kill) && state =/= s_ready && r_naccBitmapOnly.get) {
        r_naccBitmapResponseStale.get := true.B
      }
      when (sfence) {
        naccBareTagValid.get := false.B
      }
      when (naccBitmapOnlyResponse) {
        assert(r_naccBitmapOnly.get, "NACC bitmap-only response without a matching NBDTLB request")
        when (!naccRootValidationOnlyResponse && state === s_wait &&
          !r_naccBitmapResponseStale.get && !sfence && !io.kill && !naccBitmapFatal) {
          naccBareTagValid.get := true.B
          naccBareTagPPN.get := r_naccBitmapPPN.get
          naccBareTag.get := io.ptw.resp.bits.naccBitmapTag.get
        }
      }
    }
    for (w <- 0 until memWidth) {
      when (io.req(w).fire && (tlb_miss(w) || naccBareBitmapMiss(w) || naccRootValidationMiss(w)) && state === s_ready) {
        state := s_request
        r_refill_tag := vpn(w)
        val naccMetadataOnly = naccBareBitmapMiss(w) || naccRootValidationMiss(w)
        r_naccBitmapOnly.foreach(_ := naccMetadataOnly)
        r_naccBitmapPPN.foreach(_ := Mux(naccRootValidationMiss(w), io.ptw.ptbr.ppn, naccBarePPN(w)))
        r_naccRootValidationOnly.foreach(_ := naccRootValidationMiss(w))
        r_naccPendingRequestEffectiveSU.foreach(_ := priv_uses_vm && !io.req(w).bits.passthrough)

        r_superpage_repl_addr := replacementEntry(superpage_entries, superpage_plru.way)
        r_sectored_repl_addr  := replacementEntry(sectored_entries, sectored_plru.way)
        r_sectored_hit_addr   := OHToUInt(sector_hits(w))
        r_sectored_hit        := sector_hits(w).orR
      }
    }
    when (state === s_request) {
      when (sfence) { state := s_ready }
      when (io.ptw.req.ready) { state := Mux(sfence, s_wait_invalidate, s_wait) }
      when (io.kill) { state := s_ready }
      when (naccPendingPTWBlocked) { state := s_ready }
    }
    when (state === s_wait && sfence) {
      state := s_wait_invalidate
    }
    when (io.ptw.resp.valid) {
      state := s_ready
    }

    when (sfence) {
      for (w <- 0 until memWidth) {
        assert(!io.sfence.bits.rs1 || (io.sfence.bits.addr >> pgIdxBits) === vpn(w))
        for (e <- all_entries) {
          when (io.sfence.bits.rs1) { e.invalidateVPN(vpn(w)) }
          .elsewhen (io.sfence.bits.rs2) { e.invalidateNonGlobal() }
          .otherwise { e.invalidate() }
        }
      }
    }
    when (multipleHits.orR || reset.asBool) {
      all_entries.foreach(_.invalidate())
    }
  }

  def replacementEntry(set: Seq[Entry], alt: UInt) = {
    val valids = set.map(_.valid.orR).asUInt
    Mux(valids.andR, alt, PriorityEncoder(~valids))
  }


}
