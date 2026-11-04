-- Prove2me | Theorems.Thm_ThreeSum_Parameters_entropy_phi_bound_w3sum_ac885d1
-- name    : ThreeSum.Parameters.entropy_phi_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:14.653196+00:00
-- url     : https://prove2.me/theorems/2db2c950-6be4-49bc-a7ec-6e7a306b8c8f
-- title:
--   Parameters: entropy phi bound
-- statement:
--   A single supporting line gives a uniform bound, including both endpoints.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L322-L339
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L322-L339

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

theorem ThreeSum.Parameters.entropy_phi_bound_w3sum_ac885d1 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    entropy t < entropyRatio * (1 + phi t) := by sorry
