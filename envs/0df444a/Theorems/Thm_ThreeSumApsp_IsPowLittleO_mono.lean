-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowLittleO_mono
-- name    : ThreeSumApsp.IsPowLittleO.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:23:04.921757+00:00
-- url     : https://prove2.me/theorems/f04227dd-7960-4c6a-8b89-7b2e32d68e4a
-- title:
--   Is Pow Little O: mono
-- statement:
--   `n^{a+o(1)} ⊆ n^{b+o(1)}` for `a ≤ b`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L86-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L86-L87

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

theorem ThreeSumApsp.IsPowLittleO.mono (h : IsPowLittleO f a) (hab : a ≤ b) : IsPowLittleO f b := by sorry
