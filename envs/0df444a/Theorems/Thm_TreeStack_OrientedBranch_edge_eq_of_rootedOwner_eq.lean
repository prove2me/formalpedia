-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_edge_eq_of_rootedOwner_eq
-- name    : TreeStack.OrientedBranch.edge_eq_of_rootedOwner_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:57:51.830461+00:00
-- url     : https://prove2.me/theorems/63777d0e-d068-410b-9c97-51cf309fa604
-- title:
--   Oriented Branch: edge eq of rooted Owner eq
-- statement:
--   The ambient-root owner assignment is injective on underlying tree edges:
--   two edges with the same owner are the same undirected edge.  Consequently its
--   restriction to any defective-edge forest is an injective incident-owner
--   assignment, without rooting forest components separately.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L155-L176
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L155-L176

import Mathlib
import Definitions.Def_TreeStack_Support
import Definitions.Def_TreeStack_ForestOwner
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.edge_eq_of_rootedOwner_eq
    (r : V) (B D : OrientedBranch T)
    (hOwner : B.rootedOwner r = D.rootedOwner r) :
    s(B.root, B.parent) = s(D.root, D.parent) := by sorry
