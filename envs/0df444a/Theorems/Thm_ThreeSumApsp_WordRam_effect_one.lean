-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_effect_one
-- name    : ThreeSumApsp.WordRam.effect_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:52.287788+00:00
-- url     : https://prove2.me/theorems/c683e792-def7-4dc8-9f7b-b0ee07a25577
-- title:
--   Word Ram: effect one
-- statement:
--   The only constant.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L285-L285
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L285-L285

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

theorem ThreeSumApsp.WordRam.effect_one (i : ℤ) : effect (.one i) m = Function.update m i (wd W 1) := by sorry
