-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_effects_append
-- name    : ThreeSumApsp.WordRam.effects_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:59:32.097826+00:00
-- url     : https://prove2.me/theorems/d22c7b4e-b04d-41b6-81fc-bdcaf92778bf
-- title:
--   Word Ram: effects append
-- statement:
--   The Word Ram construction uses the effects append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L250-L252
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L250-L252

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

theorem ThreeSumApsp.WordRam.effects_append (l₁ l₂ : List Instr) (m : ℤ → BitVec W) :
    effects (l₁ ++ l₂) m = effects l₂ (effects l₁ m) := by sorry
