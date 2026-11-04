-- Prove2me | Theorems.Thm_ThreeSum_TernaryParameters_Halpha_bounds
-- name    : ThreeSum.TernaryParameters.Halpha_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:14:31.975035+00:00
-- url     : https://prove2.me/theorems/556e3170-0149-4067-ad2a-a206a85e5ea3
-- title:
--   Ternary Parameters: Halpha bounds
-- statement:
--   The Ternary Parameters construction uses the Halpha bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L316-L329
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L316-L329

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

theorem ThreeSum.TernaryParameters.Halpha_bounds : (5114333534032641009 / 10000000000000000000 : ℝ) ≤ Halpha ∧ Halpha ≤ (2557166767016320507 / 5000000000000000000 : ℝ) := by sorry
