-- Prove2me | Theorems.Thm_ThreeSum_LightReportingWantedRecord_program_meets
-- name    : ThreeSum.LightReportingWantedRecord.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T18:12:58.893597+00:00
-- url     : https://prove2.me/theorems/201215cf-2442-4001-bd1b-7c2cd8636833
-- title:
--   Execute a decoded wanted record using retained source and reporting banks
-- statement:
--   Let a wanted item $w$ refer to a physical source incidence in a band-record list and a correctly decoded global output. Its owning $B,C$ bands are valid, its key congruence holds, and $p>0$ satisfies $4p\le p_h^J$. Fix $K\le\lfloor13J/20\rfloor$ and $K\le J$.
--
--   Assume exact source-pair, source-bank, cover, reporting-bank, selection-record, layout-record, and decoder data. The stated source endpoints, bank ordering, wanted buffers, per-level query scratch, record-space, word, and depth bounds hold; the retained counter and threshold are $o,\theta$. Let $I_w$ be the raw incidence set restricted to the owner record and its two bands, with root mass $m$. Then
--   $$r\in\{0,1\},\qquad r=1\iff\theta<o+m\ \lor\ \operatorname{Terminal}(w,K),\qquad\nu(\mathrm{counter})=o+m.$$
--   The terminal predicate means a retained frontier completion finds an exact integer match in the selected bands. Time is the wanted-item budget plus $4000$; memory below the packed-row base is preserved except the counter.
--
--   This connects the generic wanted routine to the actual decoded records and shared banks.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedRecord.lean#L25-L186

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_LightReportingWantedRecordCall_program_meets
import Theorems.Thm_ThreeSum_LightReportingWanted_program_meets
import Theorems.Thm_ThreeSum_LocalHashMoments_hitCount_cap
import Theorems.Thm_ThreeSum_OutputDecodeRecords_global_record_block
import Theorems.Thm_ThreeSum_OutputDecodeRecords_localRecords_getD
import Theorems.Thm_ThreeSum_Radix_representations_card_le
import Theorems.Thm_ThreeSum_RawReporting_partitionWord_length
import Theorems.Thm_ThreeSum_RawReporting_word_children
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow
import Theorems.Thm_ThreeSum_ReportingHostMasks_localChildren_mem
import Theorems.Thm_ThreeSum_ReportingHostWantedRecordData_cover_scalars
import Theorems.Thm_ThreeSum_Reporting_frontier_length_le_mass
import Theorems.Thm_ThreeSum_SharedReportingBankSources_source_bounds


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.ReportingHostWantedRecordData
end ThreeSum.ReportingHostWantedRecordData
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SharedReportingBankSources
end ThreeSum.SharedReportingBankSources
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

theorem ThreeSum.LightReportingWantedRecord.program_meets : ∀ {lim : Light.Limits} {μ fA fB fC : Nat → Int}
  {n NB NC g pair bank cover h J p occ srcB srcC report output dst counter K old threshold V d i : Nat}
  {rs : List.{0} ThreeSum.BandCandidateRows.Record} {shift : Int}
  (w : ThreeSum.RawReporting.Wanted.{0} h J (ThreeSum.ReportingHostWantedOriginal.AType n g rs))
  (HP : ThreeSum.SourceBandPairData.Stored μ fB fC pair NB NC g p (ThreeSum.BlockSourceEncoding.modulus h J) shift)
  (HB :
    ThreeSum.SourceBandBankData.Stored μ fB fC bank NB NC g h J (ThreeSum.LightBlockQuery.sourceCut h J) occ
      (@Nat.cast.{0} Int instNatCastInt p) shift)
  (HC : ThreeSum.LightCoverKeyData.Stored μ cover h J)
  (HQ : ThreeSum.SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (@Nat.cast.{0} Int instNatCastInt p) shift)
  (hi :
    @LT.lt.{0} Nat instLTNat
      (ThreeSum.BandRawA.ownerRecord n g rs
          (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w))).b
      (ThreeSum.BandPartition.size NB g))
  (hj :
    @LT.lt.{0} Nat instLTNat
      (ThreeSum.BandRawA.ownerRecord n g rs
          (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w))).c
      (ThreeSum.BandPartition.size NC g))
  (houtput :
    @LT.lt.{0} Nat instLTNat output
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (ThreeSum.OutputDecodeRecords.localCount h) J))
  (he :
    @Eq.{1} (ThreeSum.GlobalEncoding.GlobalOutput h J)
      (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (ThreeSum.GlobalEncoding.GlobalOutput h J)
        (@Prod.snd.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J))
          w))
      (ThreeSum.LightOutputDecodeOriginal.output h J output))
  (hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hguard :
    @LE.le.{0} Int Int.instLEInt
      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) (@Nat.cast.{0} Int instNatCastInt p))
      (ThreeSum.GlobalEncoding.globalModulus h J))
  (hK : @LE.le.{0} Nat instLENat K (ThreeSum.LightSwitchDepth.depth J)) (hKJ : @LE.le.{0} Nat instLENat K J)
  (hkey :
    @Dvd.dvd.{0} Int Int.instDvd (ThreeSum.GlobalEncoding.globalModulus h J)
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
              (ThreeSum.BandRawA.valueAt n g rs fA
                (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
                  (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt p))
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (ThreeSum.RawIncidences.lift
                (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput h J)
                  (@Prod.snd.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt p)))
          shift)
        (@ThreeSum.GlobalEncoding.globalKey h J
          (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J)
            (@Prod.snd.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w)))))
  (hselected :
    Light.Seg μ (ThreeSum.ReportingHostWantedLayout.access dst J)
      (ThreeSum.ReportingHostWantedControls.record
        (ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w
          output)))
  (hlayout :
    Light.SegN μ dst
      (ThreeSum.ReportingHostWantedLayout.values
        (ThreeSum.LightReportingWantedLayout.layout dst h J K
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) NB NC)))
  (hdecoded :
    ThreeSum.LightWantedDecode.Stored μ (ThreeSum.ReportingHostWantedLayout.decoded dst)
      (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) h J i output)
  (hcounter :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      dst)
  (hcounterRead : @Eq.{1} Int (μ counter) (@Nat.cast.{0} Int instNatCastInt old))
  (hthreshold :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Nat.cast.{0} Int instNatCastInt threshold))
  (hends :
    ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
      (ThreeSum.LightReportingWantedAccess.selection n g rs
        (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
          (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
            (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput h J))
            w))
        pair bank cover NB NC h J (ThreeSum.LightBlockQuery.sourceCut h J) occ
        (ThreeSum.OutputDecodeOccurrenceCode.code (ThreeSum.GlobalEncoding.scheduleSize h)
          (ThreeSum.OutputDecodeRecords.layerCount h) J output))
      pair bank cover srcB srcC
      (ThreeSum.BandRawA.ownerRecord n g rs
          (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w))).b
      (ThreeSum.BandRawA.ownerRecord n g rs
          (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w))).c
      (ThreeSum.OutputDecodeOccurrenceCode.code (ThreeSum.GlobalEncoding.scheduleSize h)
        (ThreeSum.OutputDecodeRecords.layerCount h) J output)
      h J (ThreeSum.LightBlockQuery.sourceCut h J) counter)
  (hbank :
    @LE.le.{0} Nat instLENat
      (ThreeSum.SourceBandBankData.finish bank NB NC g h J (ThreeSum.LightBlockQuery.sourceCut h J)) report)
  (hreport : @LE.le.{0} Nat instLENat (ThreeSum.SharedReportingBankHeader.finish report h J NB NC g) counter)
  (hbuffers :
    ThreeSum.SharedReportingBankResourceBounds.WantedBuffers lim dst h J K
      (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) NB NC V)
  (hqueries :
    ∀ (k : Nat),
      @LE.le.{0} Nat instLENat k K →
        ThreeSum.ReportingHostLevelData.Scratch lim h J k
          (ThreeSum.ReportingHostWantedRecordData.catalogs n NB NC g report h J rs w output k)
          (@Finset.card.{0} (Fin NB)
            (ThreeSum.BandRawA.finiteBandPositions NB g
              (ThreeSum.BandRawA.ownerRecord n g rs
                  (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
                    (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
                      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (ThreeSum.GlobalEncoding.GlobalOutput h J))
                      w))).b))
          (@Finset.card.{0} (Fin NC)
            (ThreeSum.BandRawA.finiteBandPositions NC g
              (ThreeSum.BandRawA.ownerRecord n g rs
                  (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
                    (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
                      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (ThreeSum.GlobalEncoding.GlobalOutput h J))
                      w))).c))
          (ThreeSum.LightReportingWantedLayout.layout dst h J K
              (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) NB NC).maskBase
          (ThreeSum.LightReportingWantedLayout.layout dst h J K
              (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) NB NC).work)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hrecordSpace :
    @LE.le.{0} Nat instLENat
      (ThreeSum.LightReportingWantedRecordCall.space (ThreeSum.ReportingHostWantedLayout.access dst J) dst cover counter
        h J K)
      lim.space)
  (hselectedWords :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int)
          (ThreeSum.ReportingHostWantedControls.record
            (ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w
              output))
          z →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z) lim.word)
  (hguardWord :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
              (@ThreeSum.ReportingHostFrontierLayout.rootMass.{0, 0, 0}
                (ThreeSum.ReportingHostWantedOriginal.AType n g rs) (Fin NB) (Fin NC)
                (instDecidableEqFin (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))) h J
                (ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w))
            threshold)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      lim.word)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightReportingTerminal.word h J)) lim.word)
  (hreadB :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NB →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB j)) (fB j))
  (hreadC :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NC →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcC j)) (fC j))
  (hvaluesB :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NB →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (fB j)) lim.word)
  (hvaluesC :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NC →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (fC j)) lim.word)
  (htarget :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NB →
        @LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (ThreeSum.BandRawA.valueAt n g rs fA
                (@Fin.val (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))
                  (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs)
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J))
                    w)))
              (fB j)))
          lim.word)
  (hcountWord :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) NB NC))
      lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (ThreeSum.SharedReportingBankResourceBounds.wantedDepth h J K
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) NB NC))
      lim.depth),
  have S :=
    ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output;
  have D := ThreeSum.ReportingHostWantedRecordData.catalogs n NB NC g report h J rs w output;
  Light.Meets lim ThreeSum.LightReportingWantedRecordCall.program
    (@OfNat.ofNat.{0} Nat (nat_lit 138) (instOfNatNat (nat_lit 138))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.ReportingHostWantedLayout.access dst J))
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt K)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BlockSourceEncoding.modulus h J))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cover)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt counter) (@List.nil.{0} Int)))))))))
    μ
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@ThreeSum.LightReportingWanted.time.{0, 0, 0} (ThreeSum.ReportingHostWantedOriginal.AType n g rs) (Fin NB)
        (Fin NC) (instDecidableEqFin (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))) h J p
        shift (@ThreeSum.ReportingHostWantedOriginal.left h J n g rs fB w)
        (@ThreeSum.ReportingHostWantedOriginal.right h J n g rs fC w) S.NL S.NR old threshold
        (ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w D K)
      (@OfNat.ofNat.{0} Nat (nat_lit 4000) (instOfNatNat (nat_lit 4000))))
    fun (r : Int) (ν : Nat → Int) =>
    And
      (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (And
        (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Or
            (@LT.lt.{0} Nat instLTNat threshold
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                (@ThreeSum.ReportingHostFrontierLayout.rootMass.{0, 0, 0}
                  (ThreeSum.ReportingHostWantedOriginal.AType n g rs) (Fin NB) (Fin NC)
                  (instDecidableEqFin (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))) h J
                  (ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w)))
            (ThreeSum.ReportingHostWantedOriginal.Terminal h J n NB NC g p rs fA fB fC shift w K)))
        (And
          (@Eq.{1} Int (ν counter)
            (@Nat.cast.{0} Int instNatCastInt
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                (@ThreeSum.ReportingHostFrontierLayout.rootMass.{0, 0, 0}
                  (ThreeSum.ReportingHostWantedOriginal.AType n g rs) (Fin NB) (Fin NC)
                  (instDecidableEqFin (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))) h J
                  (ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w))))
          (Light.KeptBut μ ν (ThreeSum.ReportingHostWantedLayout.packed dst J) counter
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  sorry
