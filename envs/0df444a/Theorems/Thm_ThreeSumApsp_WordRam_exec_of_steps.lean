-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_exec_of_steps
-- name    : ThreeSumApsp.WordRam.exec_of_steps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:53.802746+00:00
-- url     : https://prove2.me/theorems/d8facb01-ff39-4a8a-8b83-01bb8c27f3a7
-- title:
--   Word Ram: exec of steps
-- statement:
--   A run that reaches a verdict.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L162-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L162-L171

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

theorem ThreeSumApsp.WordRam.exec_of_steps {n : ℕ} {c c' : Cfg W} {v : Bool} (h : Steps P n c c')
    (hv : step P c' = .inr v) : exec P (n + 1) c.pc c.mem = some (v, c'.mem) := by sorry
