-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_step_accept
-- name    : ThreeSumApsp.WordRam.step_accept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:50.286267+00:00
-- url     : https://prove2.me/theorems/26495be3-2865-4e51-8787-f19dde2ca9e7
-- title:
--   Word Ram: step accept
-- statement:
--   The Word Ram construction uses the step accept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L352-L353
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L352-L353

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

theorem ThreeSumApsp.WordRam.step_accept {c : Cfg W} (h : P.getD c.pc .reject = .accept) : step P c = .inr true := by sorry
