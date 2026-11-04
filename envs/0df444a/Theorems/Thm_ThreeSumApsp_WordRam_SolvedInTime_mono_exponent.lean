-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_SolvedInTime_mono_exponent
-- name    : ThreeSumApsp.WordRam.SolvedInTime.mono_exponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:58.090205+00:00
-- url     : https://prove2.me/theorems/f34bc036-5248-4d50-b38f-ff547497db42
-- title:
--   Solved In Time: mono exponent
-- statement:
--   A bound `O(n^a (log n)^e)` is a bound `O(n^a' (log n)^e)` for `a ≤ a'`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L175-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L175-L179

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr)
open Filter

theorem ThreeSumApsp.WordRam.SolvedInTime.mono_exponent {Q : EndStatement.Problem} {a a' : ℝ} {e : ℕ}
    (h : SolvedInTime Q a e) (ha : a ≤ a') : SolvedInTime Q a' e := by sorry
