-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_sparse_query_access_bound
-- name    : ThreeSum.SparseBoxes.sparse_query_access_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:03:15.921205+00:00
-- url     : https://prove2.me/theorems/1cb5a127-6231-4729-abe9-47b537781430
-- title:
--   Sparse Boxes: sparse query access bound
-- statement:
--   The exact query identity uses at most a polynomial factor times `choose(mu,t)`
--   leaf evaluations and box lookups. The work-item domains above enumerate just
--   the required cardinality layers.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L591-L599
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L591-L599

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

theorem ThreeSum.SparseBoxes.sparse_query_access_bound (q : Finset α) (t : ℕ) (ht : t ≤ q.card / 2) :
    (explicitLeaves q t).card + (q.powersetCard t).card ≤
      ((q.card + 1) ^ 2 + 1) * q.card.choose t := by sorry
