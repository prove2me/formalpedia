-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_reverse_child_occupied_of_supportEdge
-- name    : TreeStack.OrientedBranch.reverse_child_occupied_of_supportEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:52:58.385029+00:00
-- url     : https://prove2.me/theorems/13589b0c-7998-5279-a835-4b82155f19b5
-- title:
--   Oriented Branch: reverse child occupied of support Edge
-- statement:
--   The occupied exterior side of a retained edge lies on the reverse side of
--   every genuine child edge.  This is the one-step separation fact that makes the
--   retained support core path-closed without changing the ambient vertex type.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L101-L116
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L101-L116

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.reverse_child_occupied_of_supportEdge
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) (c : B.Child) :
    (B.childBranch c).reverseBranch.Occupied C := by sorry
