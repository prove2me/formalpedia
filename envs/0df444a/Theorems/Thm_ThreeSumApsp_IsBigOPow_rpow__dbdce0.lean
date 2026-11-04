-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_rpow__dbdce0
-- name    : ThreeSumApsp.IsBigOPow.rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:45.072875+00:00
-- url     : https://prove2.me/theorems/dbdce06a-f5ce-4237-b440-1ffc32ebcbc4
-- title:
--   Is Big OPow: rpow
-- statement:
--   `O(n^a) ^ r = O(n^(a r))` for a real exponent `r ≥ 0`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L92-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L92-L95

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

theorem ThreeSumApsp.IsBigOPow.rpow (hf : IsBigOPow f a) {r : ℝ} (hr : 0 ≤ r) :
    IsBigOPow (fun n => f n ^ r) (a * r) := by sorry
