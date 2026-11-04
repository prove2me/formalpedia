-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans_union
-- name    : ThreeSumApsp.WordRam.AgreeOutside.trans_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:59.894504+00:00
-- url     : https://prove2.me/theorems/680ceb92-c611-4252-9ad5-682688a52175
-- title:
--   Agree Outside: trans union
-- statement:
--   A change inside s, then a change inside t.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L377-L379
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L377-L379

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

theorem ThreeSumApsp.WordRam.AgreeOutside.trans_union (h₁ : AgreeOutside s m₁ m₂) (h₂ : AgreeOutside t m₂ m₃) :
    AgreeOutside (s ∪ t) m₁ m₃ := by sorry
