-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowPolylog_of_abs_le
-- name    : ThreeSumApsp.IsPowPolylog.of_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:29.468187+00:00
-- url     : https://prove2.me/theorems/89db1979-5064-4342-b611-3f94cd31f27f
-- title:
--   Is Pow Polylog: of abs le
-- statement:
--   A bound `|f n| ≤ C * (n ^ a * (log n) ^ e)` from some `n₀` on gives `f = Õ(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L194-L196
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L194-L196

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

theorem ThreeSumApsp.IsPowPolylog.of_abs_le (C : ℝ) (e n₀ : ℕ)
    (h : ∀ n, n₀ ≤ n → |f n| ≤ C * ((n : ℝ) ^ a * Real.log n ^ e)) : IsPowPolylog f a := by sorry
