-- Prove2me | Theorems.Thm_Real_log_two_lt_one
-- name    : Real.log_two_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:57.445978+00:00
-- url     : https://prove2.me/theorems/04d3a5f6-ea6b-49ac-b388-33358132ad96
-- title:
--   Real: log two lt one
-- statement:
--   `log 2 < 1`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L36-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L36-L37

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
set_option autoImplicit false
section
open Real

theorem Real.log_two_lt_one : log 2 < 1 := by sorry
