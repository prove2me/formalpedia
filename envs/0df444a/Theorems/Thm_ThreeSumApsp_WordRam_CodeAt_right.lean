-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_right
-- name    : ThreeSumApsp.WordRam.CodeAt.right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:58:24.079308+00:00
-- url     : https://prove2.me/theorems/1e0dddd9-64c9-462a-8bc7-cb13f11d715e
-- title:
--   Code At: right
-- statement:
--   The second part of a piece of code follows the first.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L200-L204
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L200-L204

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

theorem ThreeSumApsp.WordRam.CodeAt.right {pos : ℕ} {l₁ l₂ : List Instr} (h : CodeAt P pos (l₁ ++ l₂)) :
    CodeAt P (pos + l₁.length) l₂ := by sorry
