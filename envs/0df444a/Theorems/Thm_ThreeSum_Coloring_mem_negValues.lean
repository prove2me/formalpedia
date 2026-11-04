-- Prove2me | Theorems.Thm_ThreeSum_Coloring_mem_negValues
-- name    : ThreeSum.Coloring.mem_negValues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:01:35.142725+00:00
-- url     : https://prove2.me/theorems/d24c4326-d37e-4e89-837a-1af2559bbc76
-- title:
--   Coloring: mem neg Values
-- statement:
--   The Coloring construction uses the mem neg Values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L158-L160
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Coloring.lean#L158-L160

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

theorem ThreeSum.Coloring.mem_negValues {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3) (v : ℤ) :
    v ∈ negValues x c ↔ ∃ i, c i = 2 ∧ -x i = v := by sorry
