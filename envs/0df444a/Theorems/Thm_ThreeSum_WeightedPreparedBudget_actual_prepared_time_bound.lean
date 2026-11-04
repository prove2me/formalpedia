-- Prove2me | Theorems.Thm_ThreeSum_WeightedPreparedBudget_actual_prepared_time_bound
-- name    : ThreeSum.WeightedPreparedBudget.actual_prepared_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:48:56.911227+00:00
-- url     : https://prove2.me/theorems/b8347b80-4004-4452-ba50-79db90188173
-- title:
--   Weighted Prepared Budget: actual prepared time bound
-- statement:
--   The Weighted Prepared Budget construction uses the actual prepared time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedBudget.lean#L20-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedBudget.lean#L20-L73

import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_PreparedBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPreparedBudget
open LightWeightedNearPair WeightedSchedule WeightedQueryBudget
open TernaryJointType
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedPreparedBudget.actual_prepared_time_bound {m : ℕ} (f g : Config)
    (hT : f.T=bankCut m) (Q : TritWord (fixedLength m)) (hQ : HasType Q (fixedPi m)) :
    (LightWeightedPreparedWanted.time f g Q : ℝ)≤
      100000*(width (fixedLength m) f g : ℝ)^3*envelope m := by sorry
