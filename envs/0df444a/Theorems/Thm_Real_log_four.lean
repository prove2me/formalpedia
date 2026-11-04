-- Prove2me | Theorems.Thm_Real_log_four
-- name    : Real.log_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:58.607598+00:00
-- url     : https://prove2.me/theorems/cc993de4-8a82-4d39-8a71-d3aeb7319273
-- title:
--   Real: log four
-- statement:
--   `log 4 = 2 log 2`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L40-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L40-L41

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
set_option autoImplicit false
section
open Real

theorem Real.log_four : log 4 = 2 * log 2 := by sorry
