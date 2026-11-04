-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_budget_bound
-- name    : ThreeSum.WeightedGlobalCoverCapParameters.budget_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:41.638452+00:00
-- url     : https://prove2.me/theorems/355ed667-1528-4036-9022-fb343bc79778
-- title:
--   Weighted Global Cover Cap Parameters: budget bound
-- statement:
--   The Weighted Global Cover Cap Parameters construction uses the budget bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverCapParameters.lean#L32-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverCapParameters.lean#L32-L49

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalCoverCapParameters
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency WeightedGlobalPartitionCount TernaryTypeLowerBound

theorem ThreeSum.WeightedGlobalCoverCapParameters.budget_bound (p B k : ℕ) : 16*p^4*B^2*3^(4*k^2) ≤ 2^capBudget p B k := by sorry
