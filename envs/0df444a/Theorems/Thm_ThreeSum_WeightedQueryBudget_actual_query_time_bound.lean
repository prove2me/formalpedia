-- Prove2me | Theorems.Thm_ThreeSum_WeightedQueryBudget_actual_query_time_bound
-- name    : ThreeSum.WeightedQueryBudget.actual_query_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:45:26.739999+00:00
-- url     : https://prove2.me/theorems/12ca2ae9-f769-46ea-9b74-bdf22477d52d
-- title:
--   Weighted Query Budget: actual query time bound
-- statement:
--   The Weighted Query Budget construction uses the actual query time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryBudget.lean#L110-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryBudget.lean#L110-L123

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

theorem ThreeSum.WeightedQueryBudget.actual_query_time_bound {m L : ℕ} (Q : TritWord (fixedLength m))
    (hQ : HasType Q (fixedPi m)) :
    (LightWeightedFrozenQuery.queryTime L (bankCut m) (fixedLength m) Q : ℝ)≤
      10000*((fixedLength m : ℝ)+L+1)*((fixedLength m : ℝ)+1)*envelope m := by sorry
