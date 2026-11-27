-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_child_supportEdge_iff_occupied_of_supportEdge
-- name    : TreeStack.OrientedBranch.child_supportEdge_iff_occupied_of_supportEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:49:38.451865+00:00
-- url     : https://prove2.me/theorems/3a16bdab-8042-4410-bbae-bc03364674dc
-- title:
--   Oriented Branch: child support Edge iff occupied of support Edge
-- statement:
--   Below a retained support edge, a genuine child edge is retained exactly
--   when its child branch contains positive support.  The occupied reverse side is
--   supplied by the exterior witness of the parent retained edge.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L121-L132
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L121-L132

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.child_supportEdge_iff_occupied_of_supportEdge
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) (c : B.Child) :
    (B.childBranch c).SupportEdge C ↔
      (B.childBranch c).Occupied C := by sorry
