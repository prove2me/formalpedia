-- Prove2me | Theorems.Thm_ThreeSumApsp_isBigOPow_natCast
-- name    : ThreeSumApsp.isBigOPow_natCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:11:39.736618+00:00
-- url     : https://prove2.me/theorems/d44c8b10-7e8d-46aa-9ffc-ef35b7095b7a
-- title:
--   Three Sum Apsp: is Big OPow nat Cast
-- statement:
--   `n = O(n^1)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L51-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L51-L52

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

theorem ThreeSumApsp.isBigOPow_natCast : IsBigOPow (fun n : ℕ => (n : ℝ)) 1 := by sorry
