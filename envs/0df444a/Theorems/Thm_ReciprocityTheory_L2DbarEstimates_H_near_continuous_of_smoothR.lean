-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_near_continuous_of_smoothR
-- name    : ReciprocityTheory.L2DbarEstimates.H.near_continuous_of_smoothR
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:58:22.773068+00:00
-- url     : https://prove2.me/theorems/f81ef4f2-1429-5d37-9b66-c9319ec41412
-- title:
--   H: near continuous of smooth R
-- statement:
--   The H construction uses the near continuous of smooth R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/NearContinuousOfSmoothR.lean#L44-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/NearContinuousOfSmoothR.lean#L44-L57

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NearContinuousOfSmoothR
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
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.H.near_continuous_of_smoothR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : SmoothR n z f) : Continuous f := by sorry
