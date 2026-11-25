-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_HSt_PCD_contDiffOn_integral__5b3d1c8257c9
-- name    : P2M_PositivityTheory_Rg_Sw_HSt_PCD_contDiffOn_integral__5b3d1c8257c9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:09:45.678485+00:00
-- url     : https://prove2.me/theorems/b0dc4ea0-2c82-43b9-9b8c-2cf75e58ef21
-- title:
--   P2 M Positivity Theory Rg Sw HSt PCD cont Diff On integral  5b3d1c8257c9: P2 M Positivity Theory Rg Sw HSt PCD cont Diff On integral  5b3d1c8257c9
-- statement:
--   The P2 M Positivity Theory Rg Sw HSt PCD cont Diff On integral  5b3d1c8257c9 construction uses the P2 M Positivity Theory Rg Sw HSt PCD cont Diff On integral  5b3d1c8257c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L163-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L163-L167

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

theorem P2M_PositivityTheory_Rg_Sw_HSt_PCD_contDiffOn_integral__5b3d1c8257c9 (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (k : F × V → E)
    (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (v : X → V) (hv : Continuous v) (h : X → ℂ) (hh : Continuous h)
    (hsupp : ∀ x ∈ Ω, ∃ W ∈ 𝓝 x, ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, k (x', v u) = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ u, h u • k (x, v u) ∂ν) Ω := by sorry

alias «PositivityTheory».«Rg».«Sw».«HSt».«PCD».«contDiffOn_integral'» := P2M_PositivityTheory_Rg_Sw_HSt_PCD_contDiffOn_integral__5b3d1c8257c9
