-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_vertices_nonempty
-- name    : TreeStack.OrientedBranch.vertices_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:10:05.837502+00:00
-- url     : https://prove2.me/theorems/48b6e113-46c0-404b-80be-d71e8fd1be58
-- title:
--   Oriented Branch: vertices nonempty
-- statement:
--   Every oriented branch is nonempty.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L66-L68
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L66-L68

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.vertices_nonempty (B : OrientedBranch T) :
    B.vertices.Nonempty := by sorry
