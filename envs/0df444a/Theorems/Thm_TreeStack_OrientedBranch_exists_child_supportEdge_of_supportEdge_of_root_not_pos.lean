-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_exists_child_supportEdge_of_supportEdge_of_root_not_pos
-- name    : TreeStack.OrientedBranch.exists_child_supportEdge_of_supportEdge_of_root_not_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:01:25.262879+00:00
-- url     : https://prove2.me/theorems/d4b3d110-4ecc-494f-b21d-b0587aa72c92
-- title:
--   Oriented Branch: exists child support Edge of support Edge of root not pos
-- statement:
--   If the root of a retained edge is not itself occupied, some retained child
--   edge continues the support core.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L175-L189
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L175-L189

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.exists_child_supportEdge_of_supportEdge_of_root_not_pos
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) (hRoot : ¬ 0 < C B.root) :
    ∃ c : B.Child, (B.childBranch c).SupportEdge C := by sorry
