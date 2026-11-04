-- Prove2me | Theorems.Thm_ThreeSumApsp_isBigOPow_const
-- name    : ThreeSumApsp.isBigOPow_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:24.701247+00:00
-- url     : https://prove2.me/theorems/66f50bf0-ddab-4760-81e3-3d53fd61e5bb
-- title:
--   Three Sum Apsp: is Big OPow const
-- statement:
--   A constant is `O(n^0)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L55-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L55-L56

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

theorem ThreeSumApsp.isBigOPow_const (c : ℝ) : IsBigOPow (fun _ => c) 0 := by sorry
