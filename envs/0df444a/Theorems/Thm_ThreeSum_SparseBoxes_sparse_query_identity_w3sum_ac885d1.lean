-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_sparse_query_identity_w3sum_ac885d1
-- name    : ThreeSum.SparseBoxes.sparse_query_identity_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:15:53.042625+00:00
-- url     : https://prove2.me/theorems/76fb2829-2509-4227-8f17-0a575ef8982e
-- title:
--   Sparse Boxes: sparse query identity
-- statement:
--   The full query partition as an exact signed-sum identity: explicit leaves
--   with fewer than `t` missing positions, plus one lookup per `t`-subset.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L520-L542
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L520-L542

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

theorem ThreeSum.SparseBoxes.sparse_query_identity_w3sum_ac885d1 (q : Finset α) (t : ℕ) (weight : Finset α → ℤ) :
    (∑ leaf ∈ q.powerset, weight leaf) =
      (∑ leaf ∈ q.powerset with (q \ leaf).card < t, weight leaf) +
      ∑ u ∈ q.powersetCard t, boxSum (q \ u) (queryFree q u) weight := by sorry
