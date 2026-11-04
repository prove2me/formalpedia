-- Prove2me | Theorems.Thm_ThreeSumApsp_isBigOPow_natCast_pow
-- name    : ThreeSumApsp.isBigOPow_natCast_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:11:48.994463+00:00
-- url     : https://prove2.me/theorems/1b6ee539-93dd-4949-a2c4-b33b30df3cdd
-- title:
--   Three Sum Apsp: is Big OPow nat Cast pow
-- statement:
--   `n ^ k = O(n^k)` for a natural number `k`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L47-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L47-L48

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

theorem ThreeSumApsp.isBigOPow_natCast_pow (k : ℕ) : IsBigOPow (fun n : ℕ => (n : ℝ) ^ k) k := by sorry
