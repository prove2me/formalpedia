-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_solvesWithin_iff
-- name    : ThreeSumApsp.WordRam.solvesWithin_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:58.304525+00:00
-- url     : https://prove2.me/theorems/3a210284-a31d-463d-b4e3-d721653ef107
-- title:
--   Word Ram: solves Within iff
-- statement:
--   `SolvesWithin` is `Solves` for the problem `ofEnd Q`, on the instances with `U = n^κ`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L76-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L76-L86

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

theorem ThreeSumApsp.WordRam.solvesWithin_iff {Q : EndStatement.Problem} {κ : ℕ} {P : List Instr} {b : ℕ} {T : ℕ → ℝ} :
    SolvesWithin Q κ P b T ↔ Solves (ofEnd Q) P b (fun x => x.U = x.n ^ κ) fun x => T x.n := by sorry
