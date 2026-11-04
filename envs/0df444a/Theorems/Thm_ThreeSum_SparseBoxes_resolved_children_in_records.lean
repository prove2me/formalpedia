-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_resolved_children_in_records
-- name    : ThreeSum.SparseBoxes.resolved_children_in_records
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:41.933424+00:00
-- url     : https://prove2.me/theorems/9a526ee4-3a47-4b7b-bde7-72d8498fa920
-- title:
--   Sparse Boxes: resolved children in records
-- statement:
--   The Sparse Boxes construction uses the resolved children in records property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L464-L482
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L464-L482

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

theorem ThreeSum.SparseBoxes.resolved_children_in_records (ambient flags free : Finset α) (cut : ℕ)
    (hfa : flags ⊆ ambient) (hcut : flags.card ≤ cut)
    (hinit : IsInitial flags free) (hn : free.Nonempty) :
    let a := free.max' hn
    (⟨flags, (free.erase a).card⟩ : Sigma (fun _ : Finset α => ℕ)) ∈ records ambient cut ∧
    (⟨flags.erase a, (free.erase a).card⟩ : Sigma (fun _ : Finset α => ℕ)) ∈
      records ambient cut ∧
    (free.erase a).card < free.card := by sorry
