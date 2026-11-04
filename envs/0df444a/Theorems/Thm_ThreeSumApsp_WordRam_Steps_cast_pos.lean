-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_Steps_cast_pos
-- name    : ThreeSumApsp.WordRam.Steps.cast_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:57.117941+00:00
-- url     : https://prove2.me/theorems/71b8a74c-4a01-4e92-b21f-55e52d37bba1
-- title:
--   Steps: cast pos
-- statement:
--   A run, with its last position written differently.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L136-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L136-L137

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

theorem ThreeSumApsp.WordRam.Steps.cast_pos {n p p' : ℕ} {c : Cfg W} {m : ℤ → BitVec W} (h : Steps P n c ⟨p, m⟩)
    (hp : p = p') : Steps P n c ⟨p', m⟩ := by sorry
