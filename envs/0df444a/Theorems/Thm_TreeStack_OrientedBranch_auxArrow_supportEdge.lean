-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxArrow_supportEdge
-- name    : TreeStack.OrientedBranch.auxArrow_supportEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:07:14.31075+00:00
-- url     : https://prove2.me/theorems/92dd3df2-a49c-5144-90b5-61c096c356a8
-- title:
--   Oriented Branch: aux Arrow support Edge
-- statement:
--   Every auxiliary arrow lies on a retained support edge.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L189-L200
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L189-L200

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxArrow_supportEdge
    (C : Configuration V) (ambientRoot : V) {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    (incidentBranch T v u (auxArrow_adj C ambientRoot hArrow)).SupportEdge C := by sorry
