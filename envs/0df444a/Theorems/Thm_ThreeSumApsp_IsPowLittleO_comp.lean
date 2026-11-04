-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowLittleO_comp
-- name    : ThreeSumApsp.IsPowLittleO.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:40:28.281898+00:00
-- url     : https://prove2.me/theorems/e963d42d-40b2-4083-83d3-ede2e7d5ea44
-- title:
--   Is Pow Little O: comp
-- statement:
--   `(n^{d+o(1)})^{c+o(1)} = n^{cd+o(1)}`: if `T(s) = s^{c+o(1)}` and `size(n) = n^{d+o(1)}` then
--   `T(size(n)) = n^{cd+o(1)}`, for `c, d ≥ 0`. The sizes need not tend to infinity.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L133-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L133-L139

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_Dominated_comp
import Theorems.Thm_ThreeSumApsp_IsBigOPow_comp
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_comp

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

theorem ThreeSumApsp.IsPowLittleO.comp (hT : IsPowLittleO T c)
    (hs : IsPowLittleO (fun n => (size n : ℝ)) d) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    IsPowLittleO (fun n => T (size n)) (c * d) := by sorry
