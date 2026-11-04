-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverCapParameters_budget_bound
-- name    : ThreeSum.TernaryCoverCapParameters.budget_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:01.75006+00:00
-- url     : https://prove2.me/theorems/5f953c09-9fc2-43f4-a4e2-66b74f4b4316
-- title:
--   Ternary Cover Cap Parameters: budget bound
-- statement:
--   The Ternary Cover Cap Parameters construction uses the budget bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverCapParameters.lean#L25-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverCapParameters.lean#L25-L42

import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverCapParameters
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps TernaryCoverFrequency TernaryPartitionCount TernaryTypeLowerBound

theorem ThreeSum.TernaryCoverCapParameters.budget_bound (p B k : ℕ) : 16*p^4*B^2*3^(4*k^2) ≤ 2^capBudget p B k := by sorry
