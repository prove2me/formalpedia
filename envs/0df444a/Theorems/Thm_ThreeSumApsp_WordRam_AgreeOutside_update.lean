-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_update
-- name    : ThreeSumApsp.WordRam.AgreeOutside.update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:58:19.457498+00:00
-- url     : https://prove2.me/theorems/8faf810e-fddd-46a6-94ac-5aaeb3120bef
-- title:
--   Agree Outside: update
-- statement:
--   Writing a cell of s.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L390-L392
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L390-L392

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
variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}

theorem ThreeSumApsp.WordRam.AgreeOutside.update (h : AgreeOutside s m m') (ha : a ∈ s) (v : BitVec W) :
    AgreeOutside s m (Function.update m' a v) := by sorry
