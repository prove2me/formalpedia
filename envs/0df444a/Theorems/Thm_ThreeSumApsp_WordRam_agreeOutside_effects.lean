-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_agreeOutside_effects
-- name    : ThreeSumApsp.WordRam.agreeOutside_effects
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:55.097915+00:00
-- url     : https://prove2.me/theorems/decb995b-52d4-4c98-aab5-f7b0ad4dceff
-- title:
--   Word Ram: agree Outside effects
-- statement:
--   Code without stores changes only the cells that its instructions name as their targets.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L409-L415
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L409-L415

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

theorem ThreeSumApsp.WordRam.agreeOutside_effects {l : List Instr} (h : ∀ i ∈ l, WritesIn s i) (m : ℤ → BitVec W) :
    AgreeOutside s m (effects l m) := by sorry
