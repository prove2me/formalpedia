-- Prove2me | Theorems.Thm_ThreeSum_TernaryDimensionBounds_bank_log_bound
-- name    : ThreeSum.TernaryDimensionBounds.bank_log_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:53:12.911498+00:00
-- url     : https://prove2.me/theorems/4be74ea8-e5b0-4395-9979-3613120567bb
-- title:
--   Ternary Dimension Bounds: bank log bound
-- statement:
--   The Ternary Dimension Bounds construction uses the bank log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryDimensionBounds.lean#L57-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryDimensionBounds.lean#L57-L74

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryDimensionBounds
open TernaryJointType TernaryLocalParameters TernaryBank TernaryParameters

theorem ThreeSum.TernaryDimensionBounds.bank_log_bound (m j : ℕ) :
    Real.log (bankSize m j : ℝ) ≤ (fixedLength (j*m) : ℝ)*Real.log 2*bankEntropy := by sorry
