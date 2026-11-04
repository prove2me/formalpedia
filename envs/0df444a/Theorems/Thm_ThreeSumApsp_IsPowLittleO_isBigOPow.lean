-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowLittleO_isBigOPow
-- name    : ThreeSumApsp.IsPowLittleO.isBigOPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:26:20.348577+00:00
-- url     : https://prove2.me/theorems/30c2833f-5661-413a-8964-697f81bd3095
-- title:
--   Is Pow Little O: is Big OPow
-- statement:
--   `n^{a+o(1)} ⊆ O(n^b)` for `a < b`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L90-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L90-L91

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_isBigOPow

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

theorem ThreeSumApsp.IsPowLittleO.isBigOPow (h : IsPowLittleO f a) (hab : a < b) : IsBigOPow f b := by sorry
