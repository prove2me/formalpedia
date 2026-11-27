-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_rootedOther_adj_rootedOwner
-- name    : TreeStack.OrientedBranch.rootedOther_adj_rootedOwner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:57:18.599578+00:00
-- url     : https://prove2.me/theorems/2ad3300f-4c37-45e9-984c-c990ee2d46c4
-- title:
--   Oriented Branch: rooted Other adj rooted Owner
-- statement:
--   The rooted owner and the other endpoint are adjacent.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L66-L73
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L66-L73

import Mathlib
import Definitions.Def_TreeStack_Support
import Definitions.Def_TreeStack_ForestOwner
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.rootedOther_adj_rootedOwner
    (r : V) (B : OrientedBranch T) :
    T.graph.Adj (B.rootedOther r) (B.rootedOwner r) := by sorry
