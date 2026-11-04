-- Prove2me | Theorems.Thm_ThreeSum_WeightedQueryBudget_gibbs_expression
-- name    : ThreeSum.WeightedQueryBudget.gibbs_expression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:44:08.440404+00:00
-- url     : https://prove2.me/theorems/d08ef0a0-41ef-467d-8887-821844a80525
-- title:
--   Weighted Query Budget: gibbs expression
-- statement:
--   The Weighted Query Budget construction uses the gibbs expression property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryBudget.lean#L32-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryBudget.lean#L32-L56

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

theorem ThreeSum.WeightedQueryBudget.gibbs_expression {m : ℕ} (Q : TritWord (fixedLength m))
    (hQ : HasType Q (fixedPi m)) :
    queryArg1^digitCount Q 1*queryArg2^digitCount Q 2/zRoot^treeBudget m=envelope m := by sorry
