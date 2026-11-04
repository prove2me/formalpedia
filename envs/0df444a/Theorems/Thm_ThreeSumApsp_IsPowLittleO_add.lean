-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowLittleO_add
-- name    : ThreeSumApsp.IsPowLittleO.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:23:22.994235+00:00
-- url     : https://prove2.me/theorems/321087c7-2696-49e1-ac4c-35e2b88c02c1
-- title:
--   Is Pow Little O: add
-- statement:
--   `n^{a+o(1)} + n^{a+o(1)} = n^{a+o(1)}`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L102-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L102-L104

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_Dominated_add
import Theorems.Thm_ThreeSumApsp_IsBigOPow_add
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_add

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

theorem ThreeSumApsp.IsPowLittleO.add (hf : IsPowLittleO f a) (hg : IsPowLittleO g a) :
    IsPowLittleO (fun n => f n + g n) a := by sorry
