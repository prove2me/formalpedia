-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_eLpNorm_two_weighted_eq
-- name    : ReciprocityTheory.L2DbarEstimates.H.eLpNorm_two_weighted_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:41.639109+00:00
-- url     : https://prove2.me/theorems/8954f1de-bbc5-4a08-9c74-1aa88a886a56
-- title:
--   H: e Lp Norm two weighted eq
-- statement:
--   The H construction uses the e Lp Norm two weighted eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/WeightedIntegralEqLintegral.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/WeightedIntegralEqLintegral.lean#L30-L34

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

theorem ReciprocityTheory.L2DbarEstimates.H.eLpNorm_two_weighted_eq (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (f : M → ℂ) :
    eLpNorm f 2 (wvol n z ψ) = wint n z f ψ ^ (1 / (2 : ℝ)) := by sorry
