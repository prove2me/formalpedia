-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWantedRecordNeed_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:58:35.253561+00:00
-- url     : https://prove2.me/theorems/63ebead1-746f-4606-99b6-2bded894f5e8
-- title:
--   A complete wanted-record call under uniform resource needs
-- statement:
--   Write $M(n)$ for the fixed reporting magnitude envelope at natural input size $n$. Let original source functions, owner records, pair catalogs, occurrence banks, cover keys, and the shared reporting bank be stored at the prescribed executable size-$n$ parameters. Fix a wanted label, its valid decoded output index, and depth $K$ no greater than terminal depth or block count. Assume $p>0$, $4p$ is at most the global modulus, the exact lifted-key divisibility condition, and the selected-control, layout, decoded-label, and counter records. Require all persistent allocation ends before the counter, source banks before reporting data, source sizes at most $n$, incidence count at most $3M(n)^3$, previous and root masses at most $3M(n)^7$, threshold at most $9M(n)^8$, original values bounded by $U$, and the wanted need record valid at the destination. The closed call returns a Boolean equal to threshold overflow or the exact terminal-hit predicate, adds the root mass to the counter, and preserves other cells before packed scratch. Its time is the exact guarded wanted time plus $4000$.
--
--   Discharges the fully concrete wanted-record execution from the uniform reservation. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingWantedRecordNeed.lean#L19-L100

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
import Definitions.Def_ThreeSum1960614_Machine_Bundle036
import Definitions.Def_ThreeSum1960614_Machine_Bundle037
import Definitions.Def_ThreeSum1960614_Machine_Bundle038
import Definitions.Def_ThreeSum1960614_Machine_Bundle039
import Definitions.Def_ThreeSum1960614_Machine_Bundle040
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
import Lean
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_BandRawA_mem_row

namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecord
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecord
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds


namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.LightReportingWantedRecordNeed
end ThreeSum.LightReportingWantedRecordNeed
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
end ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum.ReportingHostWantedControls
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData
open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
set_option linter.unusedSectionVars false

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed.program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
    {n U NA NB NC pair bank cover p occ srcB srcC records report output dst counter K old threshold d i : ℕ}
    {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (_root_.ThreeSum.ReportingHostWantedOriginal.AType NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs))
    (HP : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fB fC pair NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) shift)
    (HB : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fB fC bank NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) occ (p : ℤ) shift)
    (HC : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ cover (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (HQ : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored μ report (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NB NC
      (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) fB fC (p : ℤ) shift)
    (hi : (_root_.ThreeSum.BandRawA.ownerRecord NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs w.1.val).b<_root_.ThreeSum.BandPartition.size NB (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))
    (hj : (_root_.ThreeSum.BandRawA.ownerRecord NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs w.1.val).c<_root_.ThreeSum.BandPartition.size NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))
    (houtput : output<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)^_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
    (he : w.2.2=_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) output)
    (hp : 0<p) (hguard : 4*(p : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hK : K≤_root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) (hKJ : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
    (hkey : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)∣ _root_.ThreeSum.BandRawA.valueAt NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs fA w.1.val%(p : ℤ)+
      _root_.ThreeSum.RawIncidences.lift w.2.1*(p : ℤ)+shift-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hselected : _root_.ThreeSum1960614.Machine.Light.Seg μ (_root_.ThreeSum.ReportingHostWantedLayout.access dst (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
      (_root_.ThreeSum.ReportingHostWantedControls.record (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) pair bank cover (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
        occ srcB srcC report rs w output)))
    (hlayout : _root_.ThreeSum1960614.Machine.Light.SegN μ dst (_root_.ThreeSum.ReportingHostWantedLayout.values (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K
      (_root_.ThreeSum.BandRawA.items NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length NB NC)))
    (hdecoded : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.Stored μ (_root_.ThreeSum.ReportingHostWantedLayout.decoded dst)
      (_root_.ThreeSum.BandRawA.items NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) i output)
    (hcounter : counter+4≤dst)
    (hcounterRead : μ counter=(old : ℤ)) (hthresholdRead : μ (counter+1)=(threshold : ℤ))
    (hends : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.selection NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs w.1.val pair bank cover NB NC
        (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) occ
        (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) output))
      pair bank cover srcB srcC (_root_.ThreeSum.BandRawA.ownerRecord NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs w.1.val).b
      (_root_.ThreeSum.BandRawA.ownerRecord NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs w.1.val).c
      (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) output)
      (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) counter)
    (hrecords : records+4*rs.length≤counter) (hsrcB : srcB+NB≤counter) (hsrcC : srcC+NC≤counter)
    (hbank : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish bank NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))≤report)
    (hreport : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish report (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)≤counter)
    (hN : (_root_.ThreeSum.BandRawA.items NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3)
    (hB : NB≤n) (hC : NC≤n)
    (hold : old≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7)
    (hmass : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p rs fA fB fC shift w) w≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7)
    (hthreshold : threshold≤9*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^8)
    (hreadB : ∀ j<NB, μ (srcB+j)=fB j) (hreadC : ∀ j<NC, μ (srcC+j)=fC j)
    (hvaluesB : ∀ j<NB, |fB j|≤(U : ℤ)) (hvaluesC : ∀ j<NC, |fC j|≤(U : ℤ))
    (hvalue : |fA (_root_.ThreeSum.BandRawA.labelAt NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs w.1.val).position|≤(U : ℤ))
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    let S := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) pair bank cover (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
      occ srcB srcC report rs w output
    let D := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.catalogs NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) report (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) rs w output
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.program 138 d
      [_root_.ThreeSum.ReportingHostWantedLayout.access dst (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n),dst,_root_.ThreeSum.SharedReportingBankResourceBounds.half n,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n,K,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n),cover,counter] μ
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.time p shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.left rs fB w) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.right rs fC w) S.NL S.NR old threshold
        (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p rs fA fB fC shift w) w D K+4000)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass
          (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p rs fA fB fC shift w) w ∨
          _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.Terminal (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p rs fA fB fC shift w K) ∧
        ν counter=((old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass
          (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p rs fA fB fC shift w) w : ℕ) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum.ReportingHostWantedLayout.packed dst (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) counter 1) := by sorry
