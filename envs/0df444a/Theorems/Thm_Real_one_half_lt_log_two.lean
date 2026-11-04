-- Prove2me | Theorems.Thm_Real_one_half_lt_log_two
-- name    : Real.one_half_lt_log_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:39.96353+00:00
-- url     : https://prove2.me/theorems/703dcf7e-7687-489b-901a-76e0ce0f33cf
-- title:
--   Real: one half lt log two
-- statement:
--   `1 / 2 < log 2`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L32-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L32-L33

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
set_option autoImplicit false
section
open Real

theorem Real.one_half_lt_log_two : 1 / 2 < log 2 := by sorry
