-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_head
-- name    : ThreeSumApsp.WordRam.CodeAt.head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:59:31.123101+00:00
-- url     : https://prove2.me/theorems/238d2810-1fa1-4d40-b4c2-8895cc69d5f9
-- title:
--   Code At: head
-- statement:
--   The first instruction of a piece of code is the one that the machine finds at its position.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L207-L213
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L207-L213

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

theorem ThreeSumApsp.WordRam.CodeAt.head {pos : ℕ} {i : Instr} {l : List Instr} (h : CodeAt P pos (i :: l)) :
    P.getD pos .reject = i := by sorry
