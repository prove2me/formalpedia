-- Prove2me | Theorems.Thm_ThreeSumApsp_isBigO_rpow_mul_log_pow_rpow
-- name    : ThreeSumApsp.isBigO_rpow_mul_log_pow_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:18.22657+00:00
-- url     : https://prove2.me/theorems/785de646-6c97-46d8-9a2d-014461b340eb
-- title:
--   Three Sum Apsp: is Big O rpow mul log pow rpow
-- statement:
--   Logarithms are absorbed: `n ^ a * (log n) ^ e = O(n ^ b)` for `a < b`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L91-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L91-L93

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp

theorem ThreeSumApsp.isBigO_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =O[atTop] fun n : ℕ => (n : ℝ) ^ b := by sorry
