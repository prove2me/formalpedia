-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_slice
-- name    : PositivityTheory.Rg.Sw.HSt.PCD.slice
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:54:53.51235+00:00
-- url     : https://prove2.me/theorems/40d6940c-3c14-5402-bccc-7fb8ec8b425a
-- title:
--   PCD: slice
-- statement:
--   The PCD construction uses the slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L117-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L117-L135

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {Ω : Set F}
omit [FiniteDimensional ℝ F]

theorem PositivityTheory.Rg.Sw.HSt.PCD.slice (hΩ : IsOpen Ω) {k : F × V → E} (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (N : ℕ) {x : F} (hx : x ∈ Ω) (w : V) :
    iteratedFDeriv ℝ N (fun x => k (x, w)) x =
      (iteratedFDeriv ℝ N k (x, w)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ F V) := by sorry
