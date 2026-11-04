-- Prove2me | Theorems.Thm_ThreeSum_Parameters_phi_step_rounding
-- name    : ThreeSum.Parameters.phi_step_rounding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:12.921201+00:00
-- url     : https://prove2.me/theorems/263fb210-1f94-4662-878b-8b5083bdc4c5
-- title:
--   Parameters: phi step rounding
-- statement:
--   The Parameters construction uses the phi step rounding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L389-L399
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L389-L399

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

theorem ThreeSum.Parameters.phi_step_rounding {u v m K : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (1 / 2)) (hv : v ∈ Icc (0 : ℝ) (1 / 2))
    (hm : 0 < m) (hstep : v - u = 1 / m) (hprev : phi u < K) :
    phi v < K + 9 / m := by sorry
