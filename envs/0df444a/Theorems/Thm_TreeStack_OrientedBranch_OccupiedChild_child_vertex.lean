-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
-- name    : TreeStack.OrientedBranch.OccupiedChild.child_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:26:33.541458+00:00
-- url     : https://prove2.me/theorems/71e4ee44-13c4-5def-bcc7-ac7933a4b4cb
-- title:
--   Occupied Child: child vertex
-- statement:
--   The Occupied Child construction uses the child vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L838-L841
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L838-L841

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]

theorem TreeStack.OrientedBranch.OccupiedChild.child_vertex
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) :
    t.child.vertex = t.1 := by sorry

attribute [defeq] TreeStack.OrientedBranch.OccupiedChild.child_vertex
