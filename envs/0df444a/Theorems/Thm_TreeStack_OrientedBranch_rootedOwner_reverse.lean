-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_reverse
-- name    : TreeStack.OrientedBranch.rootedOwner_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:56:40.484564+00:00
-- url     : https://prove2.me/theorems/8a8fc437-adda-49ff-af39-707b980baad7
-- title:
--   Oriented Branch: rooted Owner reverse
-- statement:
--   Reversing the presentation of an edge does not change its rooted owner.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L179-L187
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L179-L187

import Mathlib
import Definitions.Def_TreeStack_Support
import Definitions.Def_TreeStack_ForestOwner
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.rootedOwner_reverse
    (r : V) (B : OrientedBranch T) :
    B.reverseBranch.rootedOwner r = B.rootedOwner r := by sorry
