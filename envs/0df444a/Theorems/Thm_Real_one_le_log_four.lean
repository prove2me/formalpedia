-- Prove2me | Theorems.Thm_Real_one_le_log_four
-- name    : Real.one_le_log_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:58.599332+00:00
-- url     : https://prove2.me/theorems/2448d099-7b53-4c8d-a2f9-a4c74717f060
-- title:
--   Real: one le log four
-- statement:
--   `1 ≤ log 4`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L48-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L48-L49

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
set_option autoImplicit false
section
open Real

theorem Real.one_le_log_four : 1 ≤ log 4 := by sorry
