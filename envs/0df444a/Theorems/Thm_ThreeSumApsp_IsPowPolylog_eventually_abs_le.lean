-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowPolylog_eventually_abs_le
-- name    : ThreeSumApsp.IsPowPolylog.eventually_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:44.406627+00:00
-- url     : https://prove2.me/theorems/b96d03a0-bfd9-45ab-94eb-9c079fbfd72b
-- title:
--   Is Pow Polylog: eventually abs le
-- statement:
--   The constant and the logarithms are absorbed: if `f = Õ(n^a)` and `a < b`, then `|f n| ≤ n ^ b`
--   for all large `n`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L285-L287
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L285-L287

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
open ThreeSumApsp.IsPowPolylog

theorem ThreeSumApsp.IsPowPolylog.eventually_abs_le (hf : IsPowPolylog f a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ b := by sorry
