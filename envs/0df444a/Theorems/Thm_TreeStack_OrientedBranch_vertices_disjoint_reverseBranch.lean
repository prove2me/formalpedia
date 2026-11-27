-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_vertices_disjoint_reverseBranch
-- name    : TreeStack.OrientedBranch.vertices_disjoint_reverseBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:48:28.919964+00:00
-- url     : https://prove2.me/theorems/73536eb9-d4ef-5e18-a786-6d39f74caa29
-- title:
--   Oriented Branch: vertices disjoint reverse Branch
-- statement:
--   The two orientations of a tree edge determine disjoint vertex sides.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L13-L43
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L13-L43

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.vertices_disjoint_reverseBranch (B : OrientedBranch T) :
    Disjoint B.vertices B.reverseBranch.vertices := by sorry
