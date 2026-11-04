-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverScale_budget_crude_upper
-- name    : ThreeSum.TernaryCoverScale.budget_crude_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:27.623226+00:00
-- url     : https://prove2.me/theorems/c661759b-20ba-4d34-a47d-a38363b8bd77
-- title:
--   Ternary Cover Scale: budget crude upper
-- statement:
--   The Ternary Cover Scale construction uses the budget crude upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L102-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L102-L107

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency

theorem ThreeSum.TernaryCoverScale.budget_crude_upper (m k : ℕ) :
    capBudget (prime m) (sourceCap m (prime m)) k ≤ 12*fixedLength m+8*k^2+26 := by sorry
