-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_effect_mul
-- name    : ThreeSumApsp.WordRam.effect_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:54.432134+00:00
-- url     : https://prove2.me/theorems/7f9c2e4a-dd99-4214-9df9-538933372081
-- title:
--   Word Ram: effect mul
-- statement:
--   The product of two known numbers.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L298-L300
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L298-L300

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

theorem ThreeSumApsp.WordRam.effect_mul (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.mul i j k) m = Function.update m i (wd W (a * b)) := by sorry
