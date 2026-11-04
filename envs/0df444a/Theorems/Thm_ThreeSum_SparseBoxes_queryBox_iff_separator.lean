-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_queryBox_iff_separator
-- name    : ThreeSum.SparseBoxes.queryBox_iff_separator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:22:42.313329+00:00
-- url     : https://prove2.me/theorems/0eff46f2-4398-4b27-8254-2d7fd6bb5339
-- title:
--   Sparse Boxes: query Box iff separator
-- statement:
--   The Sparse Boxes construction uses the query Box iff separator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L110-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L110-L144

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

theorem ThreeSum.SparseBoxes.queryBox_iff_separator (q u leaf : Finset α) (huq : u ⊆ q) :
    QueryBox q u leaf ↔
      leaf ⊆ q ∧ u ⊆ q \ leaf ∧
        ∀ a ∈ u, ∀ x ∈ q \ leaf, x ∉ u → x < a := by sorry
