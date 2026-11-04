-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_steps_store
-- name    : ThreeSumApsp.WordRam.steps_store
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:09.957338+00:00
-- url     : https://prove2.me/theorems/a43945bd-4aa7-4c0b-a302-735c3bd7a0bf
-- title:
--   Word Ram: steps store
-- statement:
--   The Word Ram construction uses the steps store property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L327-L330
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L327-L330

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

theorem ThreeSumApsp.WordRam.steps_store {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.store i j :: rest))
    (hi : m i = wd W a) (ha : InRange W a) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m a (m j)⟩ := by sorry
