-- Prove2me | Theorems.Thm_ThreeSumApsp_UpperPowPolylog_const_mul
-- name    : ThreeSumApsp.UpperPowPolylog.const_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:45:52.633411+00:00
-- url     : https://prove2.me/theorems/c7b4716d-392a-4834-a5d3-7c32e61dffc2
-- title:
--   Upper Pow Polylog: const mul
-- statement:
--   Nonnegative constant factors are absorbed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L116-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L116-L120

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_Dominated_const_mul
import Theorems.Thm_ThreeSumApsp_IsBigOPow_const_mul
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_const_mul
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_const_mul

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowPolylog

theorem ThreeSumApsp.UpperPowPolylog.const_mul (hf : UpperPowPolylog f a) {c : ℝ} (hc : 0 ≤ c) :
    UpperPowPolylog (fun n => c * f n) a := by sorry
