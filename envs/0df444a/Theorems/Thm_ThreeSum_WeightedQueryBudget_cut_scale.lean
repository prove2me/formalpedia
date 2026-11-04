-- Prove2me | Theorems.Thm_ThreeSum_WeightedQueryBudget_cut_scale
-- name    : ThreeSum.WeightedQueryBudget.cut_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:45:58.691405+00:00
-- url     : https://prove2.me/theorems/8217f978-c9c1-44df-91fc-dfa2dc23652a
-- title:
--   Weighted Query Budget: cut scale
-- statement:
--   The Weighted Query Budget construction uses the cut scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryBudget.lean#L24-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/QueryBudget.lean#L24-L25

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

theorem ThreeSum.WeightedQueryBudget.cut_scale (m : ℕ) : (bankCut m : ℝ)=(fixedLength m : ℝ)*cutSlope := by sorry
