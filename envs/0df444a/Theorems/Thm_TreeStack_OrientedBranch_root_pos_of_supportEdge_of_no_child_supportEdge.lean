-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_root_pos_of_supportEdge_of_no_child_supportEdge
-- name    : TreeStack.OrientedBranch.root_pos_of_supportEdge_of_no_child_supportEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:01:08.083438+00:00
-- url     : https://prove2.me/theorems/4f65fe1f-7086-5e91-800c-9bbcfa1fe46b
-- title:
--   Oriented Branch: root pos of support Edge of no child support Edge
-- statement:
--   If an edge is retained by the support core and there is no retained child
--   edge at its root, then that root is occupied.  This is the in-place form of
--   the statement that every leaf of the minimal connected support subtree is
--   occupied.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L196-L226
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L196-L226

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.root_pos_of_supportEdge_of_no_child_supportEdge
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hNoChild : ∀ c : B.Child, ¬ (B.childBranch c).SupportEdge C) :
    0 < C B.root := by sorry
