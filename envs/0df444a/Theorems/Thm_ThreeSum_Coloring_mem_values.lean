-- Prove2me | Theorems.Thm_ThreeSum_Coloring_mem_values
-- name    : ThreeSum.Coloring.mem_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:59:41.066415+00:00
-- url     : https://prove2.me/theorems/9cb17efc-f976-4cff-b950-5f66d2944d10
-- title:
--   Coloring: mem values
-- statement:
--   The Coloring construction uses the mem values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L153-L156
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L153-L156

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Coloring
set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}

theorem ThreeSum.Coloring.mem_values {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3)
    (color : Fin 3) (v : ℤ) :
    v ∈ values x c color ↔ ∃ i, c i = color ∧ x i = v := by sorry
