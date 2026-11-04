-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_cell
-- name    : ThreeSumApsp.WordRam.AgreeOutside.cell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:01:44.459775+00:00
-- url     : https://prove2.me/theorems/0151ae67-cf38-4c78-98dc-02525db5d781
-- title:
--   Agree Outside: cell
-- statement:
--   A cell outside s is unchanged.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L382-L382
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L382-L382

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
variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}

theorem ThreeSumApsp.WordRam.AgreeOutside.cell (h : AgreeOutside s m m') (ha : a ∉ s) : m' a = m a := by sorry
