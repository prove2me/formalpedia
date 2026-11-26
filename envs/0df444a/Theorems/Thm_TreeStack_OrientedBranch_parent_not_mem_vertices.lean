-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices
-- name    : TreeStack.OrientedBranch.parent_not_mem_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:09:28.083196+00:00
-- url     : https://prove2.me/theorems/a05323c4-a4d5-4dec-80f2-bc053f4d50fb
-- title:
--   Oriented Branch: parent not mem vertices
-- statement:
--   In a tree, the parent endpoint is not in the root-side component after
--   deleting the boundary edge.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L47-L63
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L47-L63

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.parent_not_mem_vertices (B : OrientedBranch T) :
    B.parent ∉ B.vertices := by sorry
