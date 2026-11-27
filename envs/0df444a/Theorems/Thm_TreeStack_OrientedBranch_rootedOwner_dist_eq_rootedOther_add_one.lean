-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_dist_eq_rootedOther_add_one
-- name    : TreeStack.OrientedBranch.rootedOwner_dist_eq_rootedOther_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:56:53.601127+00:00
-- url     : https://prove2.me/theorems/2ff1172a-dd70-5458-ae94-e6f1005b0861
-- title:
--   Oriented Branch: rooted Owner dist eq rooted Other add one
-- statement:
--   The owner is exactly one level farther from the fixed root than the other
--   endpoint.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L77-L89
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L77-L89

import Mathlib
import Definitions.Def_TreeStack_Support
import Definitions.Def_TreeStack_ForestOwner
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.rootedOwner_dist_eq_rootedOther_add_one
    (r : V) (B : OrientedBranch T) :
    T.graph.dist r (B.rootedOwner r) =
      T.graph.dist r (B.rootedOther r) + 1 := by sorry
