-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowPolylog_isPowLittleO
-- name    : ThreeSumApsp.IsPowPolylog.isPowLittleO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:34.969844+00:00
-- url     : https://prove2.me/theorems/62945fd0-38aa-4181-af58-98328297096f
-- title:
--   Is Pow Polylog: is Pow Little O
-- statement:
--   `O(n^a (log n)^{O(1)}) ⊆ n^{a+o(1)}`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L98-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L98-L99

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

theorem ThreeSumApsp.IsPowPolylog.isPowLittleO (h : IsPowPolylog f a) : IsPowLittleO f a := by sorry
