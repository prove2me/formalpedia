-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_childBranch_vertices_subset
-- name    : TreeStack.OrientedBranch.childBranch_vertices_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:10:20.550478+00:00
-- url     : https://prove2.me/theorems/f4a60417-2b90-4ead-a3f3-a2629949ccd7
-- title:
--   Oriented Branch: child Branch vertices subset
-- statement:
--   Every vertex on a genuine child side also lies on the parent branch side.
--   The proof uses the fact that both deleted edges are bridges in the tree:
--   a walk in the child side cannot cross the parent's boundary edge without first
--   reaching the parent-branch root while avoiding the child edge.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L130-L172
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L130-L172

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.childBranch_vertices_subset (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).vertices ⊆ B.vertices := by sorry
