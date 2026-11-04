-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
-- name    : ThreeSumApsp.WordRam.Steps.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:58:05.115831+00:00
-- url     : https://prove2.me/theorems/00d9f933-530b-460f-b11e-d1f3ed9c7b85
-- title:
--   Steps: trans
-- statement:
--   One run after the other.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L126-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L126-L133

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

theorem ThreeSumApsp.WordRam.Steps.trans {n k : ℕ} {c c₁ c₂ : Cfg W} (h₁ : Steps P n c c₁) (h₂ : Steps P k c₁ c₂) :
    Steps P (n + k) c c₂ := by sorry
