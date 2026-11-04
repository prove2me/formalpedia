-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_isPowPolylog_log_natCast
-- name    : ThreeSumApsp.IsBigOPow.isPowPolylog_log_natCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:14.803982+00:00
-- url     : https://prove2.me/theorems/aeb2bd03-3d34-4e0c-ad43-5784a5cf8061
-- title:
--   Is Big OPow: is Pow Polylog log nat Cast
-- statement:
--   If `size n = O(n^μ)` for some `μ`, then `log (size n) = Õ(1)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L292-L304
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L292-L304

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

theorem ThreeSumApsp.IsBigOPow.isPowPolylog_log_natCast {size : ℕ → ℕ} {μ : ℝ}
    (hsize : IsBigOPow (fun n => (size n : ℝ)) μ) :
    IsPowPolylog (fun n => Real.log (size n)) 0 := by sorry
