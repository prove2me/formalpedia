-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_eq_parent_of_mem_vertices
-- name    : TreeStack.OrientedBranch.rootedOwner_eq_parent_of_mem_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:56:57.993707+00:00
-- url     : https://prove2.me/theorems/dbaff3d3-d962-5b19-b225-78d603e18b91
-- title:
--   Oriented Branch: rooted Owner eq parent of mem vertices
-- statement:
--   If the ambient root lies on the displayed root side of an edge, the
--   farther endpoint (and hence the rooted owner) is the displayed parent.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L93-L104
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L93-L104

import Mathlib
import Definitions.Def_TreeStack_Support
import Definitions.Def_TreeStack_ForestOwner
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.rootedOwner_eq_parent_of_mem_vertices
    (r : V) (B : OrientedBranch T) (hr : r ∈ B.vertices) :
    B.rootedOwner r = B.parent := by sorry
