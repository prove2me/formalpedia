-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_eq_of_adj_owner_of_dist
-- name    : TreeStack.OrientedBranch.eq_of_adj_owner_of_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:57:19.121803+00:00
-- url     : https://prove2.me/theorems/70344070-cdba-5829-a49f-1fddc17d11d7
-- title:
--   Oriented Branch: eq of adj owner of dist
-- statement:
--   A vertex has at most one adjacent predecessor that is exactly one level
--   closer to a fixed root in a tree.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L120-L149
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L120-L149

import Mathlib
import Definitions.Def_TreeStack_Support
import Definitions.Def_TreeStack_ForestOwner
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.eq_of_adj_owner_of_dist
    (r x u v : V)
    (hu : T.graph.Adj u x) (hv : T.graph.Adj v x)
    (hdu : T.graph.dist r x = T.graph.dist r u + 1)
    (hdv : T.graph.dist r x = T.graph.dist r v + 1) :
    u = v := by sorry
