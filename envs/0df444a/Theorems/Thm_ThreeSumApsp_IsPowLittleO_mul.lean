-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowLittleO_mul
-- name    : ThreeSumApsp.IsPowLittleO.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:58.844705+00:00
-- url     : https://prove2.me/theorems/0ff741bd-30c4-469d-87b9-2796f363b6fd
-- title:
--   Is Pow Little O: mul
-- statement:
--   `n^{a+o(1)} · n^{b+o(1)} = n^{a+b+o(1)}`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L107-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L107-L110

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_Dominated_mul
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mul
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mul

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

theorem ThreeSumApsp.IsPowLittleO.mul (hf : IsPowLittleO f a) (hg : IsPowLittleO g b) :
    IsPowLittleO (fun n => f n * g n) (a + b) := by sorry
