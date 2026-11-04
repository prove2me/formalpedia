-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_sparse_query_identity_enumerated
-- name    : ThreeSum.SparseBoxes.sparse_query_identity_enumerated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:15:55.13394+00:00
-- url     : https://prove2.me/theorems/24f8ee7c-80f8-497c-ab1a-2f0fc20cd9dd
-- title:
--   Sparse Boxes: sparse query identity enumerated
-- statement:
--   Query identity using the cardinality-layer enumeration of explicit leaves.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L602-L607
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L602-L607

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

theorem ThreeSum.SparseBoxes.sparse_query_identity_enumerated (q : Finset α) (t : ℕ)
    (weight : Finset α → ℤ) :
    (∑ leaf ∈ q.powerset, weight leaf) =
      (∑ leaf ∈ explicitLeaves q t, weight leaf) +
      ∑ u ∈ q.powersetCard t, boxSum (q \ u) (queryFree q u) weight := by sorry
