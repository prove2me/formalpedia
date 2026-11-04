-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_SolvedInPolylogTime_solvedInTime
-- name    : ThreeSumApsp.WordRam.SolvedInPolylogTime.solvedInTime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:30.370293+00:00
-- url     : https://prove2.me/theorems/fa1d4a07-f8e8-4300-a2bc-d8813ec30e6d
-- title:
--   Solved In Polylog Time: solved In Time
-- statement:
--   A bound `O(n^a (log n)^{O(1)})` is a bound `O(n^a')` for `a < a'`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L187-L191
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L187-L191

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

theorem ThreeSumApsp.WordRam.SolvedInPolylogTime.solvedInTime {Q : EndStatement.Problem} {a a' : ℝ}
    (h : SolvedInPolylogTime Q a) (ha : a < a') : SolvedInTime Q a' 0 := by sorry
