-- Prove2me | Theorems.Thm_ThreeSum_TernaryParameters_deficit_room
-- name    : ThreeSum.TernaryParameters.deficit_room
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:08.252241+00:00
-- url     : https://prove2.me/theorems/0fb4ef0a-bd1f-4090-b8ac-7ddb963cdd52
-- title:
--   Ternary Parameters: deficit room
-- statement:
--   The Ternary Parameters construction uses the deficit room property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L385-L386
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L385-L386

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

theorem ThreeSum.TernaryParameters.deficit_room : mean / 2 - deficit = (1190021 / 12500000 : ℝ) := by sorry
