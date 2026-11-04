-- Prove2me | Theorems.Thm_ThreeSum_WeightedPreparedBudget_query_max_bound
-- name    : ThreeSum.WeightedPreparedBudget.query_max_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:49:28.689698+00:00
-- url     : https://prove2.me/theorems/4e2e5b6e-b1e1-4e96-90f4-b2a62ba93d6a
-- title:
--   Weighted Prepared Budget: query max bound
-- statement:
--   The Weighted Prepared Budget construction uses the query max bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedBudget.lean#L89-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedBudget.lean#L89-L105

import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_PreparedBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPreparedBudget
open LightWeightedNearPair WeightedSchedule WeightedQueryBudget
open TernaryJointType
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedPreparedBudget.query_max_bound {m : ℕ} (f g : Config) (hT : f.T=bankCut m) :
    (queryMax m f g : ℝ)≤100000*(width (fixedLength m) f g : ℝ)^3*envelope m := by sorry
