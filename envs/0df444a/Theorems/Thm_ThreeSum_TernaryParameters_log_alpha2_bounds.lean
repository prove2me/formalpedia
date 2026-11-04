-- Prove2me | Theorems.Thm_ThreeSum_TernaryParameters_log_alpha2_bounds
-- name    : ThreeSum.TernaryParameters.log_alpha2_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:44:04.864198+00:00
-- url     : https://prove2.me/theorems/94327b07-6673-4d36-9516-5fb917c2bb31
-- title:
--   Ternary Parameters: log alpha2 bounds
-- statement:
--   The Ternary Parameters construction uses the log alpha2 bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L189-L197
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L189-L197

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

theorem ThreeSum.TernaryParameters.log_alpha2_bounds :
    (-115678545096113538599 / 25000000000000000000 : ℝ) ≤ Real.log alpha2 ∧ Real.log alpha2 ≤ (-7229909068507096161 / 1562500000000000000 : ℝ) := by sorry
