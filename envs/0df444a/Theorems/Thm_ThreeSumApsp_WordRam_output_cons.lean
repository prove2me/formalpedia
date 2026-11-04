-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_output_cons
-- name    : ThreeSumApsp.WordRam.output_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:27.301198+00:00
-- url     : https://prove2.me/theorems/834023fb-02b0-40a5-920c-822a2f597035
-- title:
--   Word Ram: output cons
-- statement:
--   `EndStatement.Problem.SolvedBy` counts the output cells as `1 + len + i`, and `output` counts
--   them as `(len + 1) + i`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L69-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L69-L73

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

theorem ThreeSumApsp.WordRam.output_cons {W : ℕ} (c : ℤ → BitVec W) (n : ℤ) (l : List ℤ) :
    (fun i : ℕ => (c ((1 + l.length + i : ℕ) : ℤ)).toInt) = output c (n :: l).length := by sorry
