-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_eq_root_or_parent
-- name    : TreeStack.OrientedBranch.rootedOwner_eq_root_or_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:07:03.753678+00:00
-- url     : https://prove2.me/theorems/d35d832c-143c-58d0-afa7-26192703c0b3
-- title:
--   Oriented Branch: rooted Owner eq root or parent
-- statement:
--   The owner of an edge is one of its endpoints.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L59-L67
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L59-L67

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.rootedOwner_eq_root_or_parent
    (ambientRoot : V) (B : OrientedBranch T) :
    B.rootedOwner ambientRoot = B.root ∨
      B.rootedOwner ambientRoot = B.parent := by sorry
