-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_vertices_union_reverseBranch
-- name    : TreeStack.OrientedBranch.vertices_union_reverseBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:00:30.356096+00:00
-- url     : https://prove2.me/theorems/c3a111cc-a8cf-4d1f-944a-bb22de7fa8d1
-- title:
--   Oriented Branch: vertices union reverse Branch
-- statement:
--   The two edge sides partition the whole finite vertex type.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L69-L74
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L69-L74

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.vertices_union_reverseBranch (B : OrientedBranch T) :
    B.vertices ∪ B.reverseBranch.vertices = (Finset.univ : Finset V) := by sorry
