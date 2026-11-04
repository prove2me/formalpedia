-- Prove2me | Theorems.Thm_ThreeSum_TernaryParameters_projection_fiber_entropy_lt_half_Hpi
-- name    : ThreeSum.TernaryParameters.projection_fiber_entropy_lt_half_Hpi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:55:26.667128+00:00
-- url     : https://prove2.me/theorems/2d322237-376e-47ee-acb1-68b50bdc0bd7
-- title:
--   Ternary Parameters: projection fiber entropy lt half Hpi
-- statement:
--   A `choose(L, alpha2*L)` fiber is strictly smaller than a half-Hpi layer.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L412-L414
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryParameters.lean#L412-L414

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

theorem ThreeSum.TernaryParameters.projection_fiber_entropy_lt_half_Hpi :
    Real.binEntropy alpha2 / Real.log 2 < Hpi / 2 := by sorry
