-- Prove2me | Theorems.Thm_ThreeSum_Parameters_tangent_right_margin
-- name    : ThreeSum.Parameters.tangent_right_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:05.910502+00:00
-- url     : https://prove2.me/theorems/f3177bcd-7b15-44ea-996b-c4d09521b504
-- title:
--   Parameters: tangent right margin
-- statement:
--   The Parameters construction uses the tangent right margin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L271-L275
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L271-L275

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

theorem ThreeSum.Parameters.tangent_right_margin :
    (1413 / 1000 : ℝ) < entropyRatio *
      (1 + phi tangentPoint + (1 / 2 - tangentPoint) * phiDeriv tangentPoint) := by sorry
