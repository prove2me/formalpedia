-- Prove2me | Theorems.Thm_ThreeSum_TernaryParameters_log_alpha0_bounds
-- name    : ThreeSum.TernaryParameters.log_alpha0_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:43:58.825215+00:00
-- url     : https://prove2.me/theorems/09fd8b0d-5a71-4a9d-9574-3a2f7d9f6a63
-- title:
--   Ternary Parameters: log alpha0 bounds
-- statement:
--   The Ternary Parameters construction uses the log alpha0 bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L143-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L143-L151

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

theorem ThreeSum.TernaryParameters.log_alpha0_bounds :
    (-10410309543098517927 / 100000000000000000000 : ℝ) ≤ Real.log alpha0 ∧ Real.log alpha0 ≤ (-10410309543098517913 / 100000000000000000000 : ℝ) := by sorry
