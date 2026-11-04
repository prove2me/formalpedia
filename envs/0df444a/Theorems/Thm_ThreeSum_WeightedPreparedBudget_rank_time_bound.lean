-- Prove2me | Theorems.Thm_ThreeSum_WeightedPreparedBudget_rank_time_bound
-- name    : ThreeSum.WeightedPreparedBudget.rank_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:48:37.2862+00:00
-- url     : https://prove2.me/theorems/a6d2f774-979c-48bb-a6aa-197cda10841d
-- title:
--   Weighted Prepared Budget: rank time bound
-- statement:
--   The Weighted Prepared Budget construction uses the rank time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedBudget.lean#L16-L18
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedBudget.lean#L16-L18

import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_PreparedBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPreparedBudget
open LightWeightedNearPair WeightedSchedule WeightedQueryBudget
open TernaryJointType
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedPreparedBudget.rank_time_bound (N : ℕ) : LightWeightedCost.time N≤2000*(N+1)^2 := by sorry
