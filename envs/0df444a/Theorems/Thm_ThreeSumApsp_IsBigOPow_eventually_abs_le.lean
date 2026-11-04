-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_eventually_abs_le
-- name    : ThreeSumApsp.IsBigOPow.eventually_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:45.5622+00:00
-- url     : https://prove2.me/theorems/ac2a35b8-6a68-4c69-ac72-2e29aca220cc
-- title:
--   Is Big OPow: eventually abs le
-- statement:
--   The constant is absorbed: if `f = O(n^a)` and `a < b`, then `|f n| ≤ n ^ b` for all large `n`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L111-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L111-L116

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsBigOPow

theorem ThreeSumApsp.IsBigOPow.eventually_abs_le (hf : IsBigOPow f a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ b := by sorry
