-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_branchMessage_congr_vertices
-- name    : TreeStack.OrientedBranch.branchMessage_congr_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:23.799963+00:00
-- url     : https://prove2.me/theorems/aed2c032-b236-5b92-a1a7-1626f5919c38
-- title:
--   Oriented Branch: branch Message congr vertices
-- statement:
--   Recursive branch messages are insensitive to configuration values outside
--   the branch.  In particular, changing a child's external boundary pile does not
--   change that child's message.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L480-L518
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L480-L518

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.branchMessage_congr_vertices
    (C D : Configuration V) (B : OrientedBranch T)
    (hCD : ∀ v ∈ B.vertices, C v = D v) :
    branchMessage C B = branchMessage D B := by sorry
