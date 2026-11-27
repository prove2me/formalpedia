-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_supportDescent_of_mem_pos
-- name    : TreeStack.OrientedBranch.supportDescent_of_mem_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:00:58.77841+00:00
-- url     : https://prove2.me/theorems/bbc74df4-ad24-557d-b8cb-79a5acff5c5c
-- title:
--   Oriented Branch: support Descent of mem pos
-- statement:
--   Every positive-support vertex on the root side of a retained edge is joined
--   to the edge root by a descent consisting entirely of retained support edges.
--   This is the rooted path-closure form of connectedness of the minimal support
--   subtree.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L150-L171
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L150-L171

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.supportDescent_of_mem_pos
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) {x : V}
    (hx : x ∈ B.vertices) (hxPos : 0 < C x) :
    SupportDescent C B x := by sorry
