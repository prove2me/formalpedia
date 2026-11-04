-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_effect_store
-- name    : ThreeSumApsp.WordRam.effect_store
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:05.29594+00:00
-- url     : https://prove2.me/theorems/0b11c578-eab4-4e33-ad16-57546c580528
-- title:
--   Word Ram: effect store
-- statement:
--   Storing at the address a that the cell i holds.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L308-L310
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L308-L310

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

theorem ThreeSumApsp.WordRam.effect_store (j : ℤ) (hi : m i = wd W a) (ha : InRange W a) :
    effect (.store i j) m = Function.update m a (m j) := by sorry
