-- Prove2me | Theorems.Thm_Real_four_le_sqrt_natCast_of_sixteen_le
-- name    : Real.four_le_sqrt_natCast_of_sixteen_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:11:33.835698+00:00
-- url     : https://prove2.me/theorems/b9bbc1c3-133b-4b49-9206-a5658149eb64
-- title:
--   Real: four le sqrt nat Cast of sixteen le
-- statement:
--   `4 ≤ √D` for a natural number `D ≥ 16`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L73-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Log.lean#L73-L74

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
set_option autoImplicit false
section
open Real

theorem Real.four_le_sqrt_natCast_of_sixteen_le {D : ℕ} (hD : 16 ≤ D) : 4 ≤ √(D : ℝ) := by sorry
