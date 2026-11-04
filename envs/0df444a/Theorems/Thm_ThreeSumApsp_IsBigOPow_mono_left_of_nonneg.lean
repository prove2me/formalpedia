-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_mono_left_of_nonneg
-- name    : ThreeSumApsp.IsBigOPow.mono_left_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:32.668544+00:00
-- url     : https://prove2.me/theorems/0b81bd69-49ff-4ae1-99e3-78b82ff7436e
-- title:
--   Is Big OPow: mono left of nonneg
-- statement:
--   If `0 ≤ f n ≤ g n` for all large `n` and `g = O(n^a)`, then `f = O(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L73-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L73-L75

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsBigOPow

theorem ThreeSumApsp.IsBigOPow.mono_left_of_nonneg (hg : IsBigOPow g a) (h0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (h : ∀ᶠ n in atTop, f n ≤ g n) : IsBigOPow f a := by sorry
