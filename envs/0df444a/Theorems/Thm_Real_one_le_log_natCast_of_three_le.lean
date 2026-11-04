-- Prove2me | Theorems.Thm_Real_one_le_log_natCast_of_three_le
-- name    : Real.one_le_log_natCast_of_three_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:03.168853+00:00
-- url     : https://prove2.me/theorems/4684e508-41fd-4647-9f36-86dee0608911
-- title:
--   Real: one le log nat Cast of three le
-- statement:
--   `1 ≤ log n` for a natural number `n ≥ 3`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L56-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L56-L57

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
set_option autoImplicit false
section
open Real

theorem Real.one_le_log_natCast_of_three_le {n : ℕ} (hn : 3 ≤ n) : 1 ≤ log n := by sorry
