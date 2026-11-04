-- Prove2me | Theorems.Thm_ThreeSumApsp_isBigO_rpow_mul_log_pow_of_le
-- name    : ThreeSumApsp.isBigO_rpow_mul_log_pow_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:04.609187+00:00
-- url     : https://prove2.me/theorems/a3ceb2fa-47db-47c6-8798-0395a4630754
-- title:
--   Three Sum Apsp: is Big O rpow mul log pow of le
-- statement:
--   `n ^ a * (log n) ^ e = O(n ^ b * (log n) ^ e')` for `a ≤ b` and `e ≤ e'`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L77-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L77-L80

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp

theorem ThreeSumApsp.isBigO_rpow_mul_log_pow_of_le {a b : ℝ} {e e' : ℕ} (hab : a ≤ b) (he : e ≤ e') :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ b * Real.log n ^ e' := by sorry
