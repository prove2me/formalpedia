-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowPolylog_pow
-- name    : ThreeSumApsp.IsPowPolylog.pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:49.406211+00:00
-- url     : https://prove2.me/theorems/45a481f9-1fd3-40ee-889f-de5c594f266c
-- title:
--   Is Pow Polylog: pow
-- statement:
--   `Õ(n^a) ^ k = Õ(n^(a k))` for a natural number `k`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L244-L248
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L244-L248

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_Dominated_pow

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsPowPolylog

theorem ThreeSumApsp.IsPowPolylog.pow (hf : IsPowPolylog f a) (k : ℕ) :
    IsPowPolylog (fun n => f n ^ k) (a * k) := by sorry
