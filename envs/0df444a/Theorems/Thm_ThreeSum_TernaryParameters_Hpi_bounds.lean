-- Prove2me | Theorems.Thm_ThreeSum_TernaryParameters_Hpi_bounds
-- name    : ThreeSum.TernaryParameters.Hpi_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:02:49.311447+00:00
-- url     : https://prove2.me/theorems/1cdd175b-48e3-4504-87f4-791379a76f42
-- title:
--   Ternary Parameters: Hpi bounds
-- statement:
--   The Ternary Parameters construction uses the Hpi bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L301-L314
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L301-L314

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

theorem ThreeSum.TernaryParameters.Hpi_bounds : (1629281449055122917 / 2000000000000000000 : ℝ) ≤ Hpi ∧ Hpi ≤ (814640724527561459 / 1000000000000000000 : ℝ) := by sorry
