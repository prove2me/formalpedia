-- Prove2me | Theorems.Thm_ThreeSumApsp_UpperPowLittleO_mono_left
-- name    : ThreeSumApsp.UpperPowLittleO.mono_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:28.647193+00:00
-- url     : https://prove2.me/theorems/3a66d892-abce-4f93-b2f1-5ea9c27d9a82
-- title:
--   Upper Pow Little O: mono left
-- statement:
--   The function may be replaced by one that is eventually at most as large.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L147-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L147-L150

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
open ThreeSumApsp.UpperPowLittleO

theorem ThreeSumApsp.UpperPowLittleO.mono_left (h : UpperPowLittleO f a) (hle : ∀ᶠ n in atTop, f' n ≤ f n) :
    UpperPowLittleO f' a := by sorry
