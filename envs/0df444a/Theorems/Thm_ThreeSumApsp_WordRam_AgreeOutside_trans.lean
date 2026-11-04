-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
-- name    : ThreeSumApsp.WordRam.AgreeOutside.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:58:12.6615+00:00
-- url     : https://prove2.me/theorems/ca48520d-7445-4845-b7b7-d1b236bedac5
-- title:
--   Agree Outside: trans
-- statement:
--   The Agree Outside construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L369-L371
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L369-L371

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

theorem ThreeSumApsp.WordRam.AgreeOutside.trans (h₁ : AgreeOutside s m₁ m₂) (h₂ : AgreeOutside s m₂ m₃) :
    AgreeOutside s m₁ m₃ := by sorry
