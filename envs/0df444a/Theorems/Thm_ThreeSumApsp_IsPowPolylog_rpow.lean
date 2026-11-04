-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowPolylog_rpow
-- name    : ThreeSumApsp.IsPowPolylog.rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:54.758126+00:00
-- url     : https://prove2.me/theorems/28357119-991e-46ed-946c-2b7ebdb14ff2
-- title:
--   Is Pow Polylog: rpow
-- statement:
--   `Õ(n^a) ^ r = Õ(n^(a r))` for a real exponent `r ≥ 0`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L251-L266
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L251-L266

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

theorem ThreeSumApsp.IsPowPolylog.rpow (hf : IsPowPolylog f a) {r : ℝ} (hr : 0 ≤ r) :
    IsPowPolylog (fun n => f n ^ r) (a * r) := by sorry
