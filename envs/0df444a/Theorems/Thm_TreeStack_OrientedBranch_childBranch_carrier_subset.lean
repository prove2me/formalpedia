-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_childBranch_carrier_subset
-- name    : TreeStack.OrientedBranch.childBranch_carrier_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:03.609825+00:00
-- url     : https://prove2.me/theorems/dfce8828-e49d-414d-b42f-719f99ce6948
-- title:
--   Oriented Branch: child Branch carrier subset
-- statement:
--   A genuine child carrier lies entirely inside the parent branch carrier.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L521-L535
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L521-L535

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.childBranch_carrier_subset
    (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).carrier ⊆ B.carrier := by sorry
