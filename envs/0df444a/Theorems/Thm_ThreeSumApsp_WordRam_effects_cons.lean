-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
-- name    : ThreeSumApsp.WordRam.effects_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:57:24.603143+00:00
-- url     : https://prove2.me/theorems/f8069c4e-9e81-41ea-8132-a31553de9d67
-- title:
--   Word Ram: effects cons
-- statement:
--   The Word Ram construction uses the effects cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L247-L248
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L247-L248

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

theorem ThreeSumApsp.WordRam.effects_cons (i : Instr) (l : List Instr) (m : ℤ → BitVec W) :
    effects (i :: l) m = effects l (effect i m) := by sorry
