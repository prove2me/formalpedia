-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_eq_emptySide_of_root_pos
-- name    : TreeStack.OrientedBranch.rootedOwner_eq_emptySide_of_root_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:10:29.492969+00:00
-- url     : https://prove2.me/theorems/f8f8dc3c-6b26-402a-bca0-f485304cf817
-- title:
--   Oriented Branch: rooted Owner eq empty Side of root pos
-- statement:
--   When the fixed ambient root carries a pebble, the empty-side endpoint of a
--   nonretained edge is exactly its rooted owner.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L399-L412
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L399-L412

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.rootedOwner_eq_emptySide_of_root_pos
    (C : Configuration V) (ambientRoot : V)
    (B : OrientedBranch T)
    (hRootPos : 0 < C ambientRoot)
    (hEmpty : ¬ B.reverseBranch.Occupied C) :
    B.rootedOwner ambientRoot = B.parent := by sorry
