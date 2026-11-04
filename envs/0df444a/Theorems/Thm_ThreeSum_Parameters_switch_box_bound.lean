-- Prove2me | Theorems.Thm_ThreeSum_Parameters_switch_box_bound
-- name    : ThreeSum.Parameters.switch_box_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:15.929656+00:00
-- url     : https://prove2.me/theorems/bbe419d6-03ec-4076-a6e5-320b6def2259
-- title:
--   Parameters: switch box bound
-- statement:
--   The Parameters construction uses the switch box bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L458-L464
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L458-L464

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

theorem ThreeSum.Parameters.switch_box_bound {a t : ℝ} (ha : a ∈ Icc (0 : ℝ) terminalFraction)
    (ht : t ∈ Icc (0 : ℝ) (1 / 2)) (hswitch : switchThreshold a ≤ phi t) :
    boxSaving ≤ 2 * bandShift - a + (1 - a) * gamma t := by sorry
