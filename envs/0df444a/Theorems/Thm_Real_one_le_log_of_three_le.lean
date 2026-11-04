-- Prove2me | Theorems.Thm_Real_one_le_log_of_three_le
-- name    : Real.one_le_log_of_three_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:00.598228+00:00
-- url     : https://prove2.me/theorems/26027696-e204-4f09-8ccd-1baebca93eaa
-- title:
--   Real: one le log of three le
-- statement:
--   `1 ≤ log x` for `x ≥ 3`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L52-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L52-L53

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
set_option autoImplicit false
section
open Real

theorem Real.one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ log x := by sorry
