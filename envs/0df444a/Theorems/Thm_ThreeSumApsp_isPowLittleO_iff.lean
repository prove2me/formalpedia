-- Prove2me | Theorems.Thm_ThreeSumApsp_isPowLittleO_iff
-- name    : ThreeSumApsp.isPowLittleO_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:04:37.560229+00:00
-- url     : https://prove2.me/theorems/da99877b-2a5e-4178-a228-64e7a12710e4
-- title:
--   Three Sum Apsp: is Pow Little O iff
-- statement:
--   `f(n) = n^{a+o(1)}` if and only if `f(n) = O(n^{a+η})` for every `η > 0`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L76-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L76-L81

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

theorem ThreeSumApsp.isPowLittleO_iff : IsPowLittleO f a ↔ ∀ η : ℝ, 0 < η → IsBigOPow f (a + η) := by sorry
