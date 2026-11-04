-- Prove2me | Theorems.Thm_Real_log_nine
-- name    : Real.log_nine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:56.934435+00:00
-- url     : https://prove2.me/theorems/714c86fc-c177-4ed7-b0d4-ff137c2d167e
-- title:
--   Real: log nine
-- statement:
--   `log 9 = 2 log 3`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L44-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L44-L45

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
set_option autoImplicit false
section
open Real

theorem Real.log_nine : log 9 = 2 * log 3 := by sorry
