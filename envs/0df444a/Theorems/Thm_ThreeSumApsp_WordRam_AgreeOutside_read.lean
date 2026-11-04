-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_read
-- name    : ThreeSumApsp.WordRam.AgreeOutside.read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:58:41.602417+00:00
-- url     : https://prove2.me/theorems/e87b70b8-9eb4-4b97-942a-5c7a9a0c4d1e
-- title:
--   Agree Outside: read
-- statement:
--   A cell outside s still holds v.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L385-L387
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Steps.lean#L385-L387

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

theorem ThreeSumApsp.WordRam.AgreeOutside.read (h : AgreeOutside s m m') (ha : a ∉ s) {v : BitVec W} (hv : m a = v) :
    m' a = v := by sorry
