-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_lintegral_abs_det_eq_lintegral_encard_3eac0b26e7a4
-- name    : P2M_GroundTheory_Heights__Heights_lintegral_abs_det_eq_lintegral_encard_3eac0b26e7a4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:48:00.356804+00:00
-- url     : https://prove2.me/theorems/a7e84e44-df06-4812-ab4e-79c41fd176ef
-- title:
--   P2 M Ground Theory Heights  Heights lintegral abs det eq lintegral encard 3eac0b26e7a4: P2 M Ground Theory Heights  Heights lintegral abs det eq lintegral encard 3eac0b26e7a4
-- statement:
--   The P2 M Ground Theory Heights  Heights lintegral abs det eq lintegral encard 3eac0b26e7a4 construction uses the P2 M Ground Theory Heights  Heights lintegral abs det eq lintegral encard 3eac0b26e7a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaMultiplicity.lean#L32-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaMultiplicity.lean#L32-L144

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaMultiplicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module Set Filter Function
open scoped ENNReal NNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_lintegral_abs_det_eq_lintegral_encard_3eac0b26e7a4 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {A : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hA : MeasurableSet A) (hf' : ∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) :
    ∫⁻ x in A, ENNReal.ofReal |(f' x).det| ∂μ =
      ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) ∂μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«lintegral_abs_det_eq_lintegral_encard» := P2M_GroundTheory_Heights__Heights_lintegral_abs_det_eq_lintegral_encard_3eac0b26e7a4
