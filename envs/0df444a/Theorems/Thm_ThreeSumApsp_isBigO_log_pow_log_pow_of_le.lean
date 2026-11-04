-- Prove2me | Theorems.Thm_ThreeSumApsp_isBigO_log_pow_log_pow_of_le
-- name    : ThreeSumApsp.isBigO_log_pow_log_pow_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:18.550819+00:00
-- url     : https://prove2.me/theorems/d919561c-2655-48ce-bc59-25ee937f47da
-- title:
--   Three Sum Apsp: is Big O log pow log pow of le
-- statement:
--   `(log n) ^ e = O((log n) ^ e')` for `e ≤ e'`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L67-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L67-L74

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp

theorem ThreeSumApsp.isBigO_log_pow_log_pow_of_le {e e' : ℕ} (he : e ≤ e') :
    (fun n : ℕ => Real.log n ^ e) =O[atTop] fun n : ℕ => Real.log n ^ e' := by sorry
