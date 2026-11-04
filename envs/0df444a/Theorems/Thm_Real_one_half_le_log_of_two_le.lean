-- Prove2me | Theorems.Thm_Real_one_half_le_log_of_two_le
-- name    : Real.one_half_le_log_of_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:11:31.451923+00:00
-- url     : https://prove2.me/theorems/d98d17ba-111e-4203-8a4e-4fa64389a3fb
-- title:
--   Real: one half le log of two le
-- statement:
--   `1 / 2 ≤ log x` for `x ≥ 2`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L60-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L60-L61

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
set_option autoImplicit false
section
open Real

theorem Real.one_half_le_log_of_two_le {x : ℝ} (hx : 2 ≤ x) : 1 / 2 ≤ log x := by sorry
