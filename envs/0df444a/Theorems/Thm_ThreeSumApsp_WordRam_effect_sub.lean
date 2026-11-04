-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_effect_sub
-- name    : ThreeSumApsp.WordRam.effect_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:01:45.604451+00:00
-- url     : https://prove2.me/theorems/ebeb3a97-330e-4c17-8218-8633937ea0b6
-- title:
--   Word Ram: effect sub
-- statement:
--   The difference of two known numbers.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L293-L295
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L293-L295

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

theorem ThreeSumApsp.WordRam.effect_sub (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.sub i j k) m = Function.update m i (wd W (a - b)) := by sorry
