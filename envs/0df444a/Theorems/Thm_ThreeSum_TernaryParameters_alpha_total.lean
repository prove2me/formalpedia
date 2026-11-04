-- Prove2me | Theorems.Thm_ThreeSum_TernaryParameters_alpha_total
-- name    : ThreeSum.TernaryParameters.alpha_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:09.676137+00:00
-- url     : https://prove2.me/theorems/9549d42f-f518-4cfc-a71c-034a11f9df13
-- title:
--   Ternary Parameters: alpha total
-- statement:
--   The Ternary Parameters construction uses the alpha total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L379-L380
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L379-L380

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

theorem ThreeSum.TernaryParameters.alpha_total : alpha0 + alpha1 + alpha2 = 1 := by sorry
