-- Prove2me | Theorems.Thm_ThreeSumApsp_eventually_mul_rpow_mul_log_pow_le
-- name    : ThreeSumApsp.eventually_mul_rpow_mul_log_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:16.526092+00:00
-- url     : https://prove2.me/theorems/61dc504b-7d4a-432f-8b93-f7a5cbdf5f7b
-- title:
--   Three Sum Apsp: eventually mul rpow mul log pow le
-- statement:
--   Constants are absorbed as well: `C * (n ^ a * (log n) ^ e) ≤ n ^ b` for all large `n`, if
--   `a < b`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L97-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L97-L103

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp

theorem ThreeSumApsp.eventually_mul_rpow_mul_log_pow_le (C : ℝ) {a b : ℝ} (hab : a < b) (e : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * ((n : ℝ) ^ a * Real.log n ^ e) ≤ (n : ℝ) ^ b := by sorry
