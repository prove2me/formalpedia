-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_mem_records
-- name    : ThreeSum.SparseBoxes.mem_records
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:21.773406+00:00
-- url     : https://prove2.me/theorems/83003919-7791-4b3e-8890-fb59bc065369
-- title:
--   Sparse Boxes: mem records
-- statement:
--   The Sparse Boxes construction uses the mem records property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L284-L287
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L284-L287

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SparseBoxes
set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]

theorem ThreeSum.SparseBoxes.mem_records (ambient flags : Finset α) (cut e : ℕ) :
    (⟨flags, e⟩ : Sigma (fun _ : Finset α => ℕ)) ∈ records ambient cut ↔
      flags ⊆ ambient ∧ flags.card ≤ cut ∧ e ≤ flags.card := by sorry
