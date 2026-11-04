-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_effect_add
-- name    : ThreeSumApsp.WordRam.effect_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:33.900783+00:00
-- url     : https://prove2.me/theorems/9f4079e2-b301-41c9-a5ef-7760d346d265
-- title:
--   Word Ram: effect add
-- statement:
--   The sum of two known numbers.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L288-L290
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L288-L290

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

theorem ThreeSumApsp.WordRam.effect_add (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.add i j k) m = Function.update m i (wd W (a + b)) := by sorry
