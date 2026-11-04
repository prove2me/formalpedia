-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_budget_crude_upper
-- name    : ThreeSum.WeightedGlobalCoverScale.budget_crude_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:19.607511+00:00
-- url     : https://prove2.me/theorems/ddd66636-f5df-4ee9-87c8-b71722dc321f
-- title:
--   Weighted Global Cover Scale: budget crude upper
-- statement:
--   The Weighted Global Cover Scale construction uses the budget crude upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L109-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L109-L114

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency

theorem ThreeSum.WeightedGlobalCoverScale.budget_crude_upper (m k : ℕ) :
    capBudget (prime m) (sourceCap m (prime m)) k ≤ 12*fixedLength m+8*k^2+26 := by sorry
