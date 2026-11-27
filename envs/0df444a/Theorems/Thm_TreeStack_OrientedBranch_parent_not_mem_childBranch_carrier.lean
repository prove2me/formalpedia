-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_childBranch_carrier
-- name    : TreeStack.OrientedBranch.parent_not_mem_childBranch_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:38.26541+00:00
-- url     : https://prove2.me/theorems/94be1c94-1555-4e8c-9eaa-e4ef860c6592
-- title:
--   Oriented Branch: parent not mem child Branch carrier
-- statement:
--   The external parent of a branch is outside every genuine child carrier.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L538-L550
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L538-L550

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.parent_not_mem_childBranch_carrier
    (B : OrientedBranch T) (c : B.Child) :
    B.parent ∉ (B.childBranch c).carrier := by sorry
