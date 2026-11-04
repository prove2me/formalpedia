-- Prove2me | Theorems.Thm_ThreeSum_WeightedQueryBudget_near_card_bound
-- name    : ThreeSum.WeightedQueryBudget.near_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:45:09.844346+00:00
-- url     : https://prove2.me/theorems/199b1be7-3b97-4f10-b9bb-01dc7689fb32
-- title:
--   Weighted Query Budget: near card bound
-- statement:
--   The Weighted Query Budget construction uses the near card bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryBudget.lean#L73-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryBudget.lean#L73-L80

import Definitions.Def_Submission_Weighted_PreparedWanted
import Definitions.Def_Submission_Weighted_Schedule
import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_Weighted_QueryBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedQueryBudget
open Real TernaryJointType WeightedSchedule WeightedCacheParameters
open WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedQueryBudget.near_card_bound {m : ℕ} (Q : TritWord (fixedLength m))
    (hQ : HasType Q (fixedPi m)) :
    ((WeightedNearBankEnumeration.nearWords Q (treeBudget m)).card : ℝ)≤envelope m := by sorry
