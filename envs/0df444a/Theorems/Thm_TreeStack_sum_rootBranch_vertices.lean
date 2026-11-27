-- Prove2me | Theorems.Thm_TreeStack_sum_rootBranch_vertices
-- name    : TreeStack.sum_rootBranch_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:51:33.357853+00:00
-- url     : https://prove2.me/theorems/f0e96b63-e8f7-5e52-b5dc-fa47fef168a4
-- title:
--   Tree Stack: sum root Branch vertices
-- statement:
--   Summing over all incident branch interiors is exactly summing over all
--   non-root vertices.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1122-L1150
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1122-L1150

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.sum_rootBranch_vertices
    (T : FiniteTree V) (r : V) (f : V → ℕ) :
    (∑ n : RootNeighbor T r, ∑ x ∈ n.branch.vertices, f x) =
      ∑ x ∈ (Finset.univ : Finset V).erase r, f x := by sorry
