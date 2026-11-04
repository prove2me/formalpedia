-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_bank_log_bound
-- name    : ThreeSum.WeightedGlobalDimensionBounds.bank_log_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:49:01.992186+00:00
-- url     : https://prove2.me/theorems/233d4e57-e499-4a7b-972d-b2434e874553
-- title:
--   Weighted Global Dimension Bounds: bank log bound
-- statement:
--   The Weighted Global Dimension Bounds construction uses the bank log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L51-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L51-L66

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters

theorem ThreeSum.WeightedGlobalDimensionBounds.bank_log_bound (m j : ℕ) : Real.log (bankSize m j : ℝ)≤
    (fixedLength (j*m) : ℝ)*Real.log 2*bankEntropy := by sorry
