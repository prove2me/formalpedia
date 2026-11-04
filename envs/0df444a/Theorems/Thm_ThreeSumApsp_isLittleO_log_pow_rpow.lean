-- Prove2me | Theorems.Thm_ThreeSumApsp_isLittleO_log_pow_rpow
-- name    : ThreeSumApsp.isLittleO_log_pow_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:18.842347+00:00
-- url     : https://prove2.me/theorems/bec128e5-4bfa-4e9c-b46f-26c9e69c5fd2
-- title:
--   Three Sum Apsp: is Little O log pow rpow
-- statement:
--   `(log n) ^ e = o(n ^ η)` for `η > 0`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L61-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L61-L64

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp

theorem ThreeSumApsp.isLittleO_log_pow_rpow {η : ℝ} (hη : 0 < η) (e : ℕ) :
    (fun n : ℕ => Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ η := by sorry
