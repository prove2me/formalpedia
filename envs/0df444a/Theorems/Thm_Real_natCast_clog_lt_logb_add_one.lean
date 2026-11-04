-- Prove2me | Theorems.Thm_Real_natCast_clog_lt_logb_add_one
-- name    : Real.natCast_clog_lt_logb_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:02.289714+00:00
-- url     : https://prove2.me/theorems/9c0224d2-2879-456e-866e-ef0ad3b3ad34
-- title:
--   Real: nat Cast clog lt logb add one
-- statement:
--   `⌈log_b n⌉ < log_b n + 1`, for all natural numbers `b` and `n` (for `b ≤ 1` or `n = 0` both
--   logarithms are `0`).
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L80-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L80-L82

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
set_option autoImplicit false
section
open Real

theorem Real.natCast_clog_lt_logb_add_one (b n : ℕ) : (Nat.clog b n : ℝ) < logb b n + 1 := by sorry
