-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_near_continuous_vsq
-- name    : ReciprocityTheory.L2DbarEstimates.H.near_continuous_vsq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:05.726135+00:00
-- url     : https://prove2.me/theorems/57ab0180-2528-42e9-bb5c-a7b4bd1e4468
-- title:
--   H: near continuous vsq
-- statement:
--   The H construction uses the near continuous vsq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/NearContinuousOfSmoothR.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/NearContinuousOfSmoothR.lean#L39-L42

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

theorem ReciprocityTheory.L2DbarEstimates.H.near_continuous_vsq {M : Type*} [TopologicalSpace M] {p : ℕ} (g : Fin p → M → ℂ)
    (hg : ∀ l, Continuous (g l)) : Continuous (fun x => vsq (gv g x)) := by sorry
