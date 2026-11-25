-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_norm_sum_mul_sq_le
-- name    : ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.norm_sum_mul_sq_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:57:58.970179+00:00
-- url     : https://prove2.me/theorems/ad189117-594a-4a1e-9641-6ea9a10c7802
-- title:
--   Skoda Operators: norm sum mul sq le
-- statement:
--   The Skoda Operators construction uses the norm sum mul sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/IntegrableSliceProdFin.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/IntegrableSliceProdFin.lean#L10-L17

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_IntegrableSliceProdFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open scoped ENNReal InnerProductSpace
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.norm_sum_mul_sq_le {p : ℕ} (g a : Fin p → ℂ) :
    ‖∑ i, g i * a i‖ ^ 2 ≤ vsq g * ∑ i, ‖a i‖ ^ 2 := by sorry
