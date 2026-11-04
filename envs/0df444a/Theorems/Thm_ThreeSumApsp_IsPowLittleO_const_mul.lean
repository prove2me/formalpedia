-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowLittleO_const_mul
-- name    : ThreeSumApsp.IsPowLittleO.const_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:49.493941+00:00
-- url     : https://prove2.me/theorems/f934a95e-6a7a-413c-b18d-ca7e9b372c19
-- title:
--   Is Pow Little O: const mul
-- statement:
--   Constant factors are absorbed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L113-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L113-L115

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_Dominated_const_mul
import Theorems.Thm_ThreeSumApsp_IsBigOPow_const_mul
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_const_mul

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

theorem ThreeSumApsp.IsPowLittleO.const_mul (hf : IsPowLittleO f a) (c : ℝ) :
    IsPowLittleO (fun n => c * f n) a := by sorry
