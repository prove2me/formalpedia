-- Prove2me | Theorems.Thm_ThreeSum_WeightedPreparedBudget_query_time_le_max
-- name    : ThreeSum.WeightedPreparedBudget.query_time_le_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:49:37.464112+00:00
-- url     : https://prove2.me/theorems/8be0be4b-aa90-41a7-aeb8-2e64ab49fbce
-- title:
--   Weighted Prepared Budget: query time le max
-- statement:
--   The Weighted Prepared Budget construction uses the query time le max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedBudget.lean#L83-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedBudget.lean#L83-L87

import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_PreparedBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPreparedBudget
open LightWeightedNearPair WeightedSchedule WeightedQueryBudget
open TernaryJointType
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedPreparedBudget.query_time_le_max {m : ℕ} (f g : Config) (Q : TritWord (fixedLength m))
    (hQ : HasType Q (fixedPi m)) :
    LightWeightedPreparedWanted.time f g Q≤queryMax m f g := by sorry
