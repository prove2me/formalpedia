-- Prove2me | Theorems.Thm_ThreeSum_TernaryParameters_endpoint_below_cut
-- name    : ThreeSum.TernaryParameters.endpoint_below_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:55:26.337458+00:00
-- url     : https://prove2.me/theorems/4e78c70b-1864-4216-9f7f-003d389b1f62
-- title:
--   Ternary Parameters: endpoint below cut
-- statement:
--   The Ternary Parameters construction uses the endpoint below cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L388-L390
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L388-L390

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

theorem ThreeSum.TernaryParameters.endpoint_below_cut : mean / 2 < mean - deficit := by sorry
