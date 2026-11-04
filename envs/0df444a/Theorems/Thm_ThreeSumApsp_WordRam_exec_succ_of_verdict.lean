-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_exec_succ_of_verdict
-- name    : ThreeSumApsp.WordRam.exec_succ_of_verdict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:05.12134+00:00
-- url     : https://prove2.me/theorems/b0b61f1e-12a3-4c49-88f4-90930446ff54
-- title:
--   Word Ram: exec succ of verdict
-- statement:
--   A step that gives a verdict ends the run.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L154-L155
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L154-L155

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}

theorem ThreeSumApsp.WordRam.exec_succ_of_verdict {c : Cfg W} {v : Bool} (h : step P c = .inr v) (t : ℕ) :
    exec P (t + 1) c.pc c.mem = some (v, c.mem) := by sorry
