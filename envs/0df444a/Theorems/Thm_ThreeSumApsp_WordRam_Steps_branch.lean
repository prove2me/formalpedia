-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_Steps_branch
-- name    : ThreeSumApsp.WordRam.Steps.branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:42.447343+00:00
-- url     : https://prove2.me/theorems/0c483ff9-e6f0-4a43-9ed3-f79d13232c5b
-- title:
--   Steps: branch
-- statement:
--   A run that ends with a branch on the sign of v, where v is negative if and only if p fails.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L344-L350
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L344-L350

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

theorem ThreeSumApsp.WordRam.Steps.branch {n l pos pos' : ℕ} {c : Cfg W} {m : ℤ → BitVec W} {v : ℤ} {p : Prop}
    (h : Steps P n c ⟨if v < 0 then l else pos, m⟩) (hv : p ↔ ¬ v < 0) (hpos : pos = pos') :
    (p → Steps P n c ⟨pos', m⟩) ∧ (¬ p → Steps P n c ⟨l, m⟩) := by sorry
