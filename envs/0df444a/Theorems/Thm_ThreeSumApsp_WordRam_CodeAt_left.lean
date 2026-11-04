-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_left
-- name    : ThreeSumApsp.WordRam.CodeAt.left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:59:22.115686+00:00
-- url     : https://prove2.me/theorems/fdf0bcab-13db-403b-86b6-eff824dcb6b2
-- title:
--   Code At: left
-- statement:
--   The first part of a piece of code.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L195-L197
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L195-L197

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

theorem ThreeSumApsp.WordRam.CodeAt.left {pos : ℕ} {l₁ l₂ : List Instr} (h : CodeAt P pos (l₁ ++ l₂)) :
    CodeAt P pos l₁ := by sorry
