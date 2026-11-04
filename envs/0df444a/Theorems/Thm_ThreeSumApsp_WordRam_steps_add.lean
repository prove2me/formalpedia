-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_steps_add
-- name    : ThreeSumApsp.WordRam.steps_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:08.101788+00:00
-- url     : https://prove2.me/theorems/f1059fd4-04e7-4128-bf54-b41c03f3f4cb
-- title:
--   Word Ram: steps add
-- statement:
--   The Word Ram construction uses the steps add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L312-L315
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L312-L315

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
variable {m : ℤ → BitVec W} {i j k a b : ℤ}

theorem ThreeSumApsp.WordRam.steps_add {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.add i j k :: rest))
    (hj : m j = wd W a) (hk : m k = wd W b) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (wd W (a + b))⟩ := by sorry
