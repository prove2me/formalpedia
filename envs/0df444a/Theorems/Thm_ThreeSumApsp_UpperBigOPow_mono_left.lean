-- Prove2me | Theorems.Thm_ThreeSumApsp_UpperBigOPow_mono_left
-- name    : ThreeSumApsp.UpperBigOPow.mono_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:02.577804+00:00
-- url     : https://prove2.me/theorems/9f32923c-de9c-4fcd-a450-6b011d443e9c
-- title:
--   Upper Big OPow: mono left
-- statement:
--   The function may be replaced by one that is eventually at most as large.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L62-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L62-L64

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_Dominated_mono_left
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono_left
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono_left

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperBigOPow

theorem ThreeSumApsp.UpperBigOPow.mono_left (h : UpperBigOPow f a) (hle : ∀ᶠ n in atTop, f' n ≤ f n) : UpperBigOPow f' a := by sorry
