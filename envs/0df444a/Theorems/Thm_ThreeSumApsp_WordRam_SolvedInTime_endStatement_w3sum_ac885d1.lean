-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_SolvedInTime_endStatement_w3sum_ac885d1
-- name    : ThreeSumApsp.WordRam.SolvedInTime.endStatement_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:47:48.852628+00:00
-- url     : https://prove2.me/theorems/6af8f302-c3c5-4d8e-a277-e05c6768080b
-- title:
--   Solved In Time: end Statement
-- statement:
--   **A bound `O(n^a)` of an item statement, with `a` the rational `r`, is the bound `O(n^r)` of the
--   end statement**, with the same program and the same slope.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Statements/Exponents.lean#L69-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Statements/Exponents.lean#L69-L79

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam

theorem ThreeSumApsp.WordRam.SolvedInTime.endStatement_w3sum_ac885d1 {Q : EndStatement.Problem} {a : ℝ} (h : SolvedInTime Q a 0)
    {r : ℚ} (hr : (r : ℝ) = a) (hr0 : 0 ≤ r) : Q.SolvedInTime r := by sorry
