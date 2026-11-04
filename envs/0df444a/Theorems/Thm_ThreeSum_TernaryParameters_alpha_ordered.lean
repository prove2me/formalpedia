-- Prove2me | Theorems.Thm_ThreeSum_TernaryParameters_alpha_ordered
-- name    : ThreeSum.TernaryParameters.alpha_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:55:25.358138+00:00
-- url     : https://prove2.me/theorems/91f31807-2708-4362-be38-b43df31abb0d
-- title:
--   Ternary Parameters: alpha ordered
-- statement:
--   The Ternary Parameters construction uses the alpha ordered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L377-L378
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L377-L378

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

theorem ThreeSum.TernaryParameters.alpha_ordered : alpha2 ≤ alpha1 ∧ alpha1 ≤ alpha0 := by sorry
