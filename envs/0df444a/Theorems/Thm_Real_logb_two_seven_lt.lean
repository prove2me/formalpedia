-- Prove2me | Theorems.Thm_Real_logb_two_seven_lt
-- name    : Real.logb_two_seven_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:11:32.209489+00:00
-- url     : https://prove2.me/theorems/4d184e28-31cd-471c-a561-e418edbb2aca
-- title:
--   Real: logb two seven lt
-- statement:
--   The exponent of Strassen's algorithm: `log₂ 7 < 59 / 21 < 2.81`, because `7 ^ 21 < 2 ^ 59`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L64-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L64-L70

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
set_option autoImplicit false
section
open Real

theorem Real.logb_two_seven_lt : logb 2 7 < 2.81 := by sorry
