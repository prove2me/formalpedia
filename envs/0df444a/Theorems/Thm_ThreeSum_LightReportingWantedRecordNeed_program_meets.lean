-- Prove2me | Theorems.Thm_ThreeSum_LightReportingWantedRecordNeed_program_meets
-- name    : ThreeSum.LightReportingWantedRecordNeed.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T18:26:16.471274+00:00
-- url     : https://prove2.me/theorems/9865d08e-aeab-41e1-827f-20ce0822ac4d
-- title:
--   The common wanted resource allocation validates a complete record call
-- statement:
--   Use the prescribed local parameters and band size for input size $n$. Let $w$ be a correctly decoded, key-consistent wanted record with valid owner bands, $p>0$, $4p\le p_h^J$, and $K\le\lfloor13J/20\rfloor$. Assume the exact source-pair, source-bank, cover, reporting, selection, layout, and decoder contracts and their stated ordering before destination $z$.
--
--   Put $M_n=2^{2048(\lfloor\log_2n\rfloor+1)}$. Require at most $3M_n^3$ physical incidences, $N_B,N_C\le n$, old count and local root mass $o,m\le3M_n^7$, and threshold $\theta\le9M_n^8$. The original $B,C$ entries and selected $A$ value are bounded by $U$, and the common wanted resource record fits at $z,d$. Then
--   $$r\in\{0,1\},\qquad r=1\iff\theta<o+m\ \lor\ \operatorname{Terminal}(w,K),\qquad\nu(\mathrm{counter})=o+m.$$
--   Execution meets the wanted-item time budget plus $4000$ and preserves memory below packed rows except the counter.
--
--   This replaces the record call's individual machine-resource obligations with the common finite allocation contract.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedRecordNeed.lean#L19-L100

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
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
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_LightReportingWantedRecord_program_meets
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_WantedSourceEnds_values
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_query_scratch
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_query_word_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_buffers
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_decoder_word_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_depth_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_numeric_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_record_space_of_ok
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_scratch_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_terminal_word_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_work_le


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
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
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
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds

theorem ThreeSum.LightReportingWantedRecordNeed.program_meets : ∀ {lim : Light.Limits} {μ fA fB fC : Nat → Int}
  {n U NA NB NC pair bank cover p occ srcB srcC records report output dst counter K old threshold d i : Nat}
  {rs : List.{0} ThreeSum.BandCandidateRows.Record} {shift : Int}
  (w :
    ThreeSum.RawReporting.Wanted.{0} (ThreeSum.SharedReportingBankResourceBounds.half n)
      (ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs))
  (HP :
    ThreeSum.SourceBandPairData.Stored μ fB fC pair NB NC (ThreeSum.BandScales.bandSize n) p
      (ThreeSum.BlockSourceEncoding.modulus (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      shift)
  (HB :
    ThreeSum.SourceBandBankData.Stored μ fB fC bank NB NC (ThreeSum.BandScales.bandSize n)
      (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (ThreeSum.LightBlockQuery.sourceCut (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      occ (@Nat.cast.{0} Int instNatCastInt p) shift)
  (HC :
    ThreeSum.LightCoverKeyData.Stored μ cover (ThreeSum.SharedReportingBankResourceBounds.half n)
      (ThreeSum.SharedReportingBankResourceBounds.blocks n))
  (HQ :
    ThreeSum.SharedReportingBankHeader.Stored μ report (ThreeSum.SharedReportingBankResourceBounds.half n)
      (ThreeSum.SharedReportingBankResourceBounds.blocks n) NB NC (ThreeSum.BandScales.bandSize n) fB fC
      (@Nat.cast.{0} Int instNatCastInt p) shift)
  (hi :
    @LT.lt.{0} Nat instLTNat
      (ThreeSum.BandRawA.ownerRecord NA (ThreeSum.BandScales.bandSize n) rs
          (@Fin.val
            (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
              w))).b
      (ThreeSum.BandPartition.size NB (ThreeSum.BandScales.bandSize n)))
  (hj :
    @LT.lt.{0} Nat instLTNat
      (ThreeSum.BandRawA.ownerRecord NA (ThreeSum.BandScales.bandSize n) rs
          (@Fin.val
            (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
              w))).c
      (ThreeSum.BandPartition.size NC (ThreeSum.BandScales.bandSize n)))
  (houtput :
    @LT.lt.{0} Nat instLTNat output
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (ThreeSum.OutputDecodeRecords.localCount (ThreeSum.SharedReportingBankResourceBounds.half n))
        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
  (he :
    @Eq.{1}
      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n))
        (@Prod.snd.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
              (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
          w))
      (ThreeSum.LightOutputDecodeOriginal.output (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n) output))
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hguard :
    @LE.le.{0} Int Int.instLEInt
      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) (@Nat.cast.{0} Int instNatCastInt p))
      (ThreeSum.GlobalEncoding.globalModulus (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
  (hK :
    @LE.le.{0} Nat instLENat K (ThreeSum.LightSwitchDepth.depth (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
  (hKJ : @LE.le.{0} Nat instLENat K (ThreeSum.SharedReportingBankResourceBounds.blocks n))
  (hkey :
    @Dvd.dvd.{0} Int Int.instDvd
      (ThreeSum.GlobalEncoding.globalModulus (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
              (ThreeSum.BandRawA.valueAt NA (ThreeSum.BandScales.bandSize n) rs fA
                (@Fin.val
                  (@List.length.{0} ThreeSum.BandRawA.Label
                    (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
                  (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt p))
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (ThreeSum.RawIncidences.lift
                (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                    (ThreeSum.SharedReportingBankResourceBounds.blocks n))
                  (@Prod.snd.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt p)))
          shift)
        (@ThreeSum.GlobalEncoding.globalKey (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n)
          (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
              (ThreeSum.SharedReportingBankResourceBounds.blocks n))
            (@Prod.snd.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
              w)))))
  (hselected :
    Light.Seg μ (ThreeSum.ReportingHostWantedLayout.access dst (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      (ThreeSum.ReportingHostWantedControls.record
        (ThreeSum.ReportingHostWantedRecordData.selected fA NA NB NC (ThreeSum.BandScales.bandSize n) pair bank cover
          (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n) occ
          srcB srcC report rs w output)))
  (hlayout :
    Light.SegN μ dst
      (ThreeSum.ReportingHostWantedLayout.values
        (ThreeSum.LightReportingWantedLayout.layout dst (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n) K
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs)) NB
          NC)))
  (hdecoded :
    ThreeSum.LightWantedDecode.Stored μ (ThreeSum.ReportingHostWantedLayout.decoded dst)
      (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
      (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n) i
      output)
  (hcounter :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      dst)
  (hcounterRead : @Eq.{1} Int (μ counter) (@Nat.cast.{0} Int instNatCastInt old))
  (hthresholdRead :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Nat.cast.{0} Int instNatCastInt threshold))
  (hends :
    ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
      (ThreeSum.LightReportingWantedAccess.selection NA (ThreeSum.BandScales.bandSize n) rs
        (@Fin.val
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
          (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
            (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
            w))
        pair bank cover NB NC (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (ThreeSum.LightBlockQuery.sourceCut (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n))
        occ
        (ThreeSum.OutputDecodeOccurrenceCode.code
          (ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.SharedReportingBankResourceBounds.half n))
          (ThreeSum.OutputDecodeRecords.layerCount (ThreeSum.SharedReportingBankResourceBounds.half n))
          (ThreeSum.SharedReportingBankResourceBounds.blocks n) output))
      pair bank cover srcB srcC
      (ThreeSum.BandRawA.ownerRecord NA (ThreeSum.BandScales.bandSize n) rs
          (@Fin.val
            (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
              w))).b
      (ThreeSum.BandRawA.ownerRecord NA (ThreeSum.BandScales.bandSize n) rs
          (@Fin.val
            (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
              w))).c
      (ThreeSum.OutputDecodeOccurrenceCode.code
        (ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.SharedReportingBankResourceBounds.half n))
        (ThreeSum.OutputDecodeRecords.layerCount (ThreeSum.SharedReportingBankResourceBounds.half n))
        (ThreeSum.SharedReportingBankResourceBounds.blocks n) output)
      (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (ThreeSum.LightBlockQuery.sourceCut (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      counter)
  (hrecords :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) records
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@List.length.{0} ThreeSum.BandCandidateRows.Record rs)))
      counter)
  (hsrcB : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB NB) counter)
  (hsrcC : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcC NC) counter)
  (hbank :
    @LE.le.{0} Nat instLENat
      (ThreeSum.SourceBandBankData.finish bank NB NC (ThreeSum.BandScales.bandSize n)
        (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (ThreeSum.LightBlockQuery.sourceCut (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
      report)
  (hreport :
    @LE.le.{0} Nat instLENat
      (ThreeSum.SharedReportingBankHeader.finish report (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n) NB NC (ThreeSum.BandScales.bandSize n))
      counter)
  (hN :
    @LE.le.{0} Nat instLENat
      (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
  (hB : @LE.le.{0} Nat instLENat NB n) (hC : @LE.le.{0} Nat instLENat NC n)
  (hold :
    @LE.le.{0} Nat instLENat old
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
  (hmass :
    @LE.le.{0} Nat instLENat
      (@ThreeSum.ReportingHostFrontierLayout.rootMass.{0, 0, 0}
        (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs) (Fin NB) (Fin NC)
        (instDecidableEqFin
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs)))
        (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (ThreeSum.ReportingHostWantedOriginal.localItems (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (ThreeSum.BandScales.bandSize n) p rs fA fB fC
          shift w)
        w)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
  (hthreshold :
    @LE.le.{0} Nat instLENat threshold
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
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
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (fB j))
          (@Nat.cast.{0} Int instNatCastInt U))
  (hvaluesC :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NC →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (fC j))
          (@Nat.cast.{0} Int instNatCastInt U))
  (hvalue :
    @LE.le.{0} Int Int.instLEInt
      (@abs.{0} Int instLatticeInt Int.instAddGroup
        (fA
          (ThreeSum.BandRawA.labelAt NA (ThreeSum.BandScales.bandSize n) rs
              (@Fin.val
                (@List.length.{0} ThreeSum.BandRawA.Label
                  (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
                (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
                  (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                      (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                  w))).position))
      (@Nat.cast.{0} Int instNatCastInt U))
  (hok : (ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d),
  have S :=
    ThreeSum.ReportingHostWantedRecordData.selected fA NA NB NC (ThreeSum.BandScales.bandSize n) pair bank cover
      (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n) occ srcB
      srcC report rs w output;
  have D :=
    ThreeSum.ReportingHostWantedRecordData.catalogs NA NB NC (ThreeSum.BandScales.bandSize n) report
      (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n) rs w
      output;
  Light.Meets lim ThreeSum.LightReportingWantedRecordCall.program
    (@OfNat.ofNat.{0} Nat (nat_lit 138) (instOfNatNat (nat_lit 138))) d
    (@List.cons.{0} Int
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.ReportingHostWantedLayout.access dst (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SharedReportingBankResourceBounds.half n))
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SharedReportingBankResourceBounds.blocks n))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt K)
              (@List.cons.{0} Int
                (@Nat.cast.{0} Int instNatCastInt
                  (ThreeSum.BlockSourceEncoding.modulus (ThreeSum.SharedReportingBankResourceBounds.half n)
                    (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cover)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt counter) (@List.nil.{0} Int)))))))))
    μ
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@ThreeSum.LightReportingWanted.time.{0, 0, 0}
        (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs) (Fin NB) (Fin NC)
        (instDecidableEqFin
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs)))
        (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n) p
        shift
        (@ThreeSum.ReportingHostWantedOriginal.left (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA (ThreeSum.BandScales.bandSize n) rs fB w)
        (@ThreeSum.ReportingHostWantedOriginal.right (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA (ThreeSum.BandScales.bandSize n) rs fC w)
        S.NL S.NR old threshold
        (ThreeSum.ReportingHostWantedOriginal.localItems (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (ThreeSum.BandScales.bandSize n) p rs fA fB fC
          shift w)
        w D K)
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
                  (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs) (Fin NB) (Fin NC)
                  (instDecidableEqFin
                    (@List.length.{0} ThreeSum.BandRawA.Label
                      (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs)))
                  (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)
                  (ThreeSum.ReportingHostWantedOriginal.localItems (ThreeSum.SharedReportingBankResourceBounds.half n)
                    (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (ThreeSum.BandScales.bandSize n) p rs
                    fA fB fC shift w)
                  w)))
            (ThreeSum.ReportingHostWantedOriginal.Terminal (ThreeSum.SharedReportingBankResourceBounds.half n)
              (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (ThreeSum.BandScales.bandSize n) p rs fA fB
              fC shift w K)))
        (And
          (@Eq.{1} Int (ν counter)
            (@Nat.cast.{0} Int instNatCastInt
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                (@ThreeSum.ReportingHostFrontierLayout.rootMass.{0, 0, 0}
                  (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs) (Fin NB) (Fin NC)
                  (instDecidableEqFin
                    (@List.length.{0} ThreeSum.BandRawA.Label
                      (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs)))
                  (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)
                  (ThreeSum.ReportingHostWantedOriginal.localItems (ThreeSum.SharedReportingBankResourceBounds.half n)
                    (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (ThreeSum.BandScales.bandSize n) p rs
                    fA fB fC shift w)
                  w))))
          (Light.KeptBut μ ν
            (ThreeSum.ReportingHostWantedLayout.packed dst (ThreeSum.SharedReportingBankResourceBounds.blocks n))
            counter (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  sorry
