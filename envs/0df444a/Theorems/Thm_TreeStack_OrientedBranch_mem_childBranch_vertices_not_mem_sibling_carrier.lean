-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_mem_childBranch_vertices_not_mem_sibling_carrier
-- name    : TreeStack.OrientedBranch.mem_childBranch_vertices_not_mem_sibling_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:39.376066+00:00
-- url     : https://prove2.me/theorems/3bce6102-6ce8-5f65-8e05-389221646e6f
-- title:
--   Oriented Branch: mem child Branch vertices not mem sibling carrier
-- statement:
--   A vertex in one child branch is outside the full carrier of every
--   distinct sibling.  The only extra carrier vertex of a child is the common
--   parent root, which lies in no child vertex set.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L631-L646
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L631-L646

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.mem_childBranch_vertices_not_mem_sibling_carrier
    (B : OrientedBranch T) (c d : B.Child)
    (hcd : c.vertex ≠ d.vertex) {w : V}
    (hw : w ∈ (B.childBranch c).vertices) :
    w ∉ (B.childBranch d).carrier := by sorry
