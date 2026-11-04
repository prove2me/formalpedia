-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_SolvedInTime_solvedInPolylogTime
-- name    : ThreeSumApsp.WordRam.SolvedInTime.solvedInPolylogTime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:32.480346+00:00
-- url     : https://prove2.me/theorems/69f51391-b196-4206-955a-688e34d44116
-- title:
--   Solved In Time: solved In Polylog Time
-- statement:
--   A bound `O(n^a (log n)^e)` is a bound `O(n^a (log n)^{O(1)})`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L182-L184
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L182-L184

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

theorem ThreeSumApsp.WordRam.SolvedInTime.solvedInPolylogTime {Q : EndStatement.Problem} {a : ℝ} {e : ℕ}
    (h : SolvedInTime Q a e) : SolvedInPolylogTime Q a := by sorry
