-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_occupied
-- name    : TreeStack.OrientedBranch.OccupiedChild.occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:27:39.774051+00:00
-- url     : https://prove2.me/theorems/839109af-d631-46c6-9e77-0d691759f4e8
-- title:
--   Occupied Child: occupied
-- statement:
--   The child represented by an occupied-child task is occupied.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L832-L836
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L832-L836

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

theorem TreeStack.OrientedBranch.OccupiedChild.occupied
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) :
    (B.childBranch t.child).Occupied C := by sorry
