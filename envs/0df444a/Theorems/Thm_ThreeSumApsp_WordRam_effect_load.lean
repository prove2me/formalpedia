-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_effect_load
-- name    : ThreeSumApsp.WordRam.effect_load
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:05.07257+00:00
-- url     : https://prove2.me/theorems/99ec1444-2cef-4a37-8566-238ca6650f5b
-- title:
--   Word Ram: effect load
-- statement:
--   Loading from the address a that the cell j holds.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L303-L305
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L303-L305

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

theorem ThreeSumApsp.WordRam.effect_load (i : ℤ) (hj : m j = wd W a) (ha : InRange W a) :
    effect (.load i j) m = Function.update m i (m a) := by sorry
