-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_queryBox_partition
-- name    : ThreeSum.SparseBoxes.queryBox_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:14:11.21542+00:00
-- url     : https://prove2.me/theorems/4fd68e1c-d3c0-44b0-bc26-3db861756cac
-- title:
--   Sparse Boxes: query Box partition
-- statement:
--   Every leaf with at least `t` missing coordinates belongs to exactly one
--   query box, namely the one indexed by its largest `t` missing coordinates.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L155-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L155-L166

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

theorem ThreeSum.SparseBoxes.queryBox_partition (q leaf : Finset α) (t : ℕ) (hlq : leaf ⊆ q)
    (ht : t ≤ (q \ leaf).card) :
    ∃! u, u ∈ q.powersetCard t ∧ QueryBox q u leaf := by sorry
