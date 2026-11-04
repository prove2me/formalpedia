-- Prove2me | Theorems.Thm_ThreeSum_TernaryParameters_log_alpha1_bounds
-- name    : ThreeSum.TernaryParameters.log_alpha1_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:43:59.269951+00:00
-- url     : https://prove2.me/theorems/aa96760f-69a8-44c7-85e8-f0c22d353b4f
-- title:
--   Ternary Parameters: log alpha1 bounds
-- statement:
--   The Ternary Parameters construction uses the log alpha1 bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L166-L174
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L166-L174

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

theorem ThreeSum.TernaryParameters.log_alpha1_bounds :
    (-48363301892258308473 / 20000000000000000000 : ℝ) ≤ Real.log alpha1 ∧ Real.log alpha1 ≤ (-30227063682661442789 / 12500000000000000000 : ℝ) := by sorry
