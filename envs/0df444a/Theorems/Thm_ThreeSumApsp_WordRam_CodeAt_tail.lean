-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_tail
-- name    : ThreeSumApsp.WordRam.CodeAt.tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:59:45.241501+00:00
-- url     : https://prove2.me/theorems/6061005b-24c7-4398-b3e2-e612f5c60ad3
-- title:
--   Code At: tail
-- statement:
--   A piece of code without its first instruction.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L216-L218
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L216-L218

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

theorem ThreeSumApsp.WordRam.CodeAt.tail {pos : ℕ} {i : Instr} {l : List Instr} (h : CodeAt P pos (i :: l)) :
    CodeAt P (pos + 1) l := by sorry
