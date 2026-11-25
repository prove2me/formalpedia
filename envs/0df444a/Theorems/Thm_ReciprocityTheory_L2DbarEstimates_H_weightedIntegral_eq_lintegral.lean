-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_weightedIntegral_eq_lintegral
-- name    : ReciprocityTheory.L2DbarEstimates.H.weightedIntegral_eq_lintegral
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:04.537467+00:00
-- url     : https://prove2.me/theorems/161be5c5-4474-5ee8-b4c5-3c1ec711a4c5
-- title:
--   H: weighted Integral eq lintegral
-- statement:
--   The H construction uses the weighted Integral eq lintegral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/WeightedIntegralEqLintegral.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/WeightedIntegralEqLintegral.lean#L19-L28

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace

theorem ReciprocityTheory.L2DbarEstimates.H.weightedIntegral_eq_lintegral (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (f : M → ℂ) :
    wint n z f ψ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂wvol n z ψ := by sorry
