-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_steps_bltz
-- name    : ThreeSumApsp.WordRam.steps_bltz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:34.711359+00:00
-- url     : https://prove2.me/theorems/64896c9d-f7a8-43d2-9442-98d9aa386a7f
-- title:
--   Word Ram: steps bltz
-- statement:
--   A branch on a cell that holds the number v: to l if v is negative, else to the next position.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L337-L341
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L337-L341

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

theorem ThreeSumApsp.WordRam.steps_bltz {rest : List Instr} {pos l : ℕ} {c v : ℤ} {m : ℤ → BitVec W}
    (hcode : CodeAt P pos (.bltz c l :: rest)) (hc : m c = wd W v) (hv : InRange W v) :
    Steps P 1 ⟨pos, m⟩ ⟨if v < 0 then l else pos + 1, m⟩ := by sorry
