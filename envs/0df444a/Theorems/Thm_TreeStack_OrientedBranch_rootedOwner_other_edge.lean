-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_other_edge
-- name    : TreeStack.OrientedBranch.rootedOwner_other_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:58:48.102528+00:00
-- url     : https://prove2.me/theorems/31e39afa-d83d-4650-bce2-f7c8d07cc264
-- title:
--   Oriented Branch: rooted Owner other edge
-- statement:
--   Reordering an edge as owner/other does not change its underlying
--   undirected edge.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L108-L116
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L108-L116

import Mathlib
import Definitions.Def_TreeStack_Support
import Definitions.Def_TreeStack_ForestOwner
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.rootedOwner_other_edge
    (r : V) (B : OrientedBranch T) :
    s(B.rootedOwner r, B.rootedOther r) =
      s(B.root, B.parent) := by sorry
