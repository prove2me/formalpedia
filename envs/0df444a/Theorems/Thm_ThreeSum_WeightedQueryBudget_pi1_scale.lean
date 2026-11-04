-- Prove2me | Theorems.Thm_ThreeSum_WeightedQueryBudget_pi1_scale
-- name    : ThreeSum.WeightedQueryBudget.pi1_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:45:54.986746+00:00
-- url     : https://prove2.me/theorems/c5e1ea63-cdd9-4e2f-8a94-59f7d9947c7b
-- title:
--   Weighted Query Budget: pi1 scale
-- statement:
--   The Weighted Query Budget construction uses the pi1 scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryBudget.lean#L20-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryBudget.lean#L20-L21

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

theorem ThreeSum.WeightedQueryBudget.pi1_scale (m : ℕ) : (fixedPi m 1 : ℝ)=(fixedLength m : ℝ)*pi1 := by sorry
