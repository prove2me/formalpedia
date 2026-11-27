-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_sum_childBranch_vertices
-- name    : TreeStack.OrientedBranch.sum_childBranch_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:51:03.868879+00:00
-- url     : https://prove2.me/theorems/abcc54fd-1891-4fab-90bb-a9b294a0132f
-- title:
--   Oriented Branch: sum child Branch vertices
-- statement:
--   Summing over every child interior is exactly summing over the non-root
--   vertices of the parent branch.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L399-L425
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L399-L425

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.sum_childBranch_vertices (B : OrientedBranch T) (f : V → ℕ) :
    (∑ c : B.Child, ∑ x ∈ (B.childBranch c).vertices, f x) =
      ∑ x ∈ B.vertices.erase B.root, f x := by sorry
