-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_childBranch_vertices_disjoint
-- name    : TreeStack.OrientedBranch.childBranch_vertices_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:31:01.909658+00:00
-- url     : https://prove2.me/theorems/6c54e410-62ac-46af-8006-0a869000dc33
-- title:
--   Oriented Branch: child Branch vertices disjoint
-- statement:
--   Distinct genuine child branches of the same oriented branch have disjoint
--   vertex sets.  A common vertex would give a path in one child component that
--   crosses the other's unique boundary edge and hence reaches the deleted parent
--   edge endpoint, contradicting the bridge separation.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L556-L625
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L556-L625

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.childBranch_vertices_disjoint
    (B : OrientedBranch T) (c d : B.Child)
    (hcd : c.vertex ≠ d.vertex) :
    Disjoint (B.childBranch c).vertices (B.childBranch d).vertices := by sorry
