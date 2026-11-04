-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_step_reject
-- name    : ThreeSumApsp.WordRam.step_reject
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:44.029656+00:00
-- url     : https://prove2.me/theorems/b49b0963-251a-4ba7-a09e-dd901965ee32
-- title:
--   Word Ram: step reject
-- statement:
--   The Word Ram construction uses the step reject property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L355-L356
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L355-L356

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

theorem ThreeSumApsp.WordRam.step_reject {c : Cfg W} (h : P.getD c.pc .reject = .reject) : step P c = .inr false := by sorry
