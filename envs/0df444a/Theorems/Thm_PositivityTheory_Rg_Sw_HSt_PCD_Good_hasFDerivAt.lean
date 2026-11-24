-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_Good_hasFDerivAt
-- name    : PositivityTheory.Rg.Sw.HSt.PCD.Good.hasFDerivAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:30.347596+00:00
-- url     : https://prove2.me/theorems/251c5c55-3d6b-4095-83e4-fd28ad879449
-- title:
--   Good: has FDeriv At
-- statement:
--   The Good construction uses the has FDeriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L49-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L49-L83

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.PCD
variable {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X] [SecondCountableTopology X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set F} {K : F → X → E}

theorem PositivityTheory.Rg.Sw.HSt.PCD.Good.hasFDerivAt [CompleteSpace E] (hΩ : IsOpen Ω) (hK : Good Ω K) (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    {x₀ : F} (hx₀ : x₀ ∈ Ω) :
    HasFDerivAt (fun x => ∫ u, K x u ∂ν) (∫ u, fderiv ℝ (K · u) x₀ ∂ν) x₀ := by sorry
