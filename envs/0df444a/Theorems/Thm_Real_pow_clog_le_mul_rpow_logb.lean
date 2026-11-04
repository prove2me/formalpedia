-- Prove2me | Theorems.Thm_Real_pow_clog_le_mul_rpow_logb
-- name    : Real.pow_clog_le_mul_rpow_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:11:36.895204+00:00
-- url     : https://prove2.me/theorems/af77f7fa-d179-4660-876f-ef434c3c8887
-- title:
--   Real: pow clog le mul rpow logb
-- statement:
--   `c ^ ⌈log_b n⌉ ≤ c * n ^ (log_b c)`, for natural numbers `b` and `n ≥ 1` and a real number
--   `c ≥ 1`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L86-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L86-L95

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
set_option autoImplicit false
section
open Real

theorem Real.pow_clog_le_mul_rpow_logb (b : ℕ) {n : ℕ} {c : ℝ} (hn : 1 ≤ n) (hc : 1 ≤ c) :
    c ^ Nat.clog b n ≤ c * (n : ℝ) ^ logb b c := by sorry
