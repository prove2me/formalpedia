-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowLittleO_eventually_abs_le
-- name    : ThreeSumApsp.IsPowLittleO.eventually_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:32:45.924111+00:00
-- url     : https://prove2.me/theorems/1216f53c-7b09-4600-a7dd-94691c18e296
-- title:
--   Is Pow Little O: eventually abs le
-- statement:
--   The `o(1)` is absorbed: if `f = n^{a+o(1)}` and `a < b`, then `|f n| ≤ n ^ b` for all large `n`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L39-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L39-L44

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_IsBigOPow_eventually_abs_le
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_eventually_abs_le

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

theorem ThreeSumApsp.IsPowLittleO.eventually_abs_le (h : IsPowLittleO f a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ b := by sorry
