-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWantedDispatchStored_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatchStored.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:03:46.046231+00:00
-- url     : https://prove2.me/theorems/4dcd741c-4db9-44cd-98a1-47ce65b40ea0
-- title:
--   Stored-data correctness of one wanted dispatcher
-- statement:
--   Write $M(n)$ for the fixed reporting magnitude envelope at natural input size $n$. Let the encoded-color pipeline and shared reporting catalog be stored with original values bounded by $U$. Fix a valid physical wanted slot whose two cells contain bounded raw and output indices decoding to the given wanted label. Assume the selected common prime is positive and at most one quarter of the global modulus, the exact lifted-key divisibility condition, correct old counter/threshold/cap cells, old and root masses at most $3M(n)^7$, threshold at most $9M(n)^8$, and a valid wanted need record one call level deeper. The dispatcher returns a Boolean equal to threshold overflow or the label's exact original terminal hit, increments the counter by its root mass, and preserves every other cell before the layout header, within its specified time.
--
--   Connects one physical pair slot to the guarded semantic reporting decision. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingWantedDispatchStored.lean#L22-L212

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle041
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
import Definitions.Def_ThreeSum1962Source_Bundle18
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
import Mathlib.Data.Finset.Image
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
import Mathlib.Data.Int.Basic
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
import Mathlib.Data.Nat.Bitwise
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
import Theorems.Thm_ThreeSum_BandCandidateRows_fromOwner_sound
import Theorems.Thm_ThreeSum_BandCandidateRows_mem_records_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_row

namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.LightReportingWantedDispatchStored
end ThreeSum.LightReportingWantedDispatchStored
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostWantedConsumerData
end ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatchStored
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatchStored
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatchStored

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
open _root_.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostWantedConsumerData
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
set_option maxHeartbeats 3800000
set_option maxRecDepth 24000
set_option linter.unusedSectionVars false

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatchStored.program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {free n U d s raw output old threshold : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (HQ : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Catalog μ free n A B C hsA hsB hsC)
    (hx : ∀ i, |x i|≤(U : ℤ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.Label n A B C hsA hsB hsC)
    (hs : s<_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)
    (hraw : raw<3*(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N)
    (hout : output<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)^_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
    (hpos : w.1.val=raw%(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N)
    (he : w.2.2=_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) output)
    (hleft : μ ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).pairs+2*s)=(raw : ℤ))
    (hright : μ ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).pairs+2*s+1)=(output : ℤ))
    (hp : 0<_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (hguard : 4*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hkey : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ∣
      _root_.ThreeSum.BandRawA.valueAt A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC) (fun j => A.getD j 0) w.1.val %
        (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      _root_.ThreeSum.RawIncidences.lift w.2.1*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hcounter : μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter=(old : ℤ))
    (hthreshold : μ ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter+1)=(threshold : ℤ))
    (hcap : μ ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter+2)=(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) : ℤ))
    (hold : old≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7)
    (hmass : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7)
    (hthresholdBound : threshold≤9*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^8)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader (d+1)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.program 151 d
      (_root_.ThreeSum.LightReportingWantedDispatch.arguments (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) s) μ
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.time (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)
        (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.recordTime free n A B C hsA hsB hsC w output old threshold))
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w ∨ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelHit n A B C hsA hsB hsC w) ∧
        ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter=((old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w : ℕ) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader
          (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter 1) := by sorry
