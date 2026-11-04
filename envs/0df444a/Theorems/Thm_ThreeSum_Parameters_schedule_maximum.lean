-- Prove2me | Theorems.Thm_ThreeSum_Parameters_schedule_maximum
-- name    : ThreeSum.Parameters.schedule_maximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:57:32.663532+00:00
-- url     : https://prove2.me/theorems/0b852cd9-51b7-41d0-afb0-8ababb2c32b1
-- title:
--   Parameters: schedule maximum
-- statement:
--   The Parameters construction uses the schedule maximum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L238-L241
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L238-L241

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

theorem ThreeSum.Parameters.schedule_maximum :
    (boxSaving - 2 * bandShift + terminalFraction) / (1 - terminalFraction)
      = (941 / 350 : ℝ) := by sorry
