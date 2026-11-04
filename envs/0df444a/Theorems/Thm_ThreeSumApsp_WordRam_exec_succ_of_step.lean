-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_exec_succ_of_step
-- name    : ThreeSumApsp.WordRam.exec_succ_of_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:06.138369+00:00
-- url     : https://prove2.me/theorems/d10835f3-e713-4882-b7fc-c50beceb7544
-- title:
--   Word Ram: exec succ of step
-- statement:
--   After a step that gives no verdict the run goes on, with one step less.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L158-L159
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L158-L159

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

theorem ThreeSumApsp.WordRam.exec_succ_of_step {c c' : Cfg W} (h : step P c = .inl c') (t : ℕ) :
    exec P (t + 1) c.pc c.mem = exec P t c'.pc c'.mem := by sorry
