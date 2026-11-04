-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_isPowLittleO
-- name    : ThreeSumApsp.IsBigOPow.isPowLittleO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:39.557781+00:00
-- url     : https://prove2.me/theorems/eacee4c3-fc76-4a07-9ea8-a7e753a23df4
-- title:
--   Is Big OPow: is Pow Little O
-- statement:
--   `O(n^a) ⊆ n^{a+o(1)}`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L94-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L94-L95

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

theorem ThreeSumApsp.IsBigOPow.isPowLittleO (h : IsBigOPow f a) : IsPowLittleO f a := by sorry
