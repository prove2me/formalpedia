-- Prove2me | Theorems.Thm_ThreeSumApsp_isLittleO_rpow_mul_log_pow_rpow
-- name    : ThreeSumApsp.isLittleO_rpow_mul_log_pow_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:24.511604+00:00
-- url     : https://prove2.me/theorems/56b78d04-cd2d-4085-afbd-9ccc9e3e186e
-- title:
--   Three Sum Apsp: is Little O rpow mul log pow rpow
-- statement:
--   Logarithms are absorbed: `n ^ a * (log n) ^ e = o(n ^ b)` for `a < b`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L83-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L83-L88

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp

theorem ThreeSumApsp.isLittleO_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ b := by sorry
