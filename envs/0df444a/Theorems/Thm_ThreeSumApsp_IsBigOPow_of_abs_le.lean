-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_of_abs_le
-- name    : ThreeSumApsp.IsBigOPow.of_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:25.302278+00:00
-- url     : https://prove2.me/theorems/8be40e88-73e9-4611-b15e-58ed9e732f4b
-- title:
--   Is Big OPow: of abs le
-- statement:
--   A bound `|f n| ≤ C * n ^ a` from some `n₀` on gives `f = O(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L61-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L61-L62

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

theorem ThreeSumApsp.IsBigOPow.of_abs_le (C : ℝ) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → |f n| ≤ C * (n : ℝ) ^ a) : IsBigOPow f a := by sorry
