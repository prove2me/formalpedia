-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_edge_leaving_vertices_eq_boundary
-- name    : TreeStack.OrientedBranch.edge_leaving_vertices_eq_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:10:22.770224+00:00
-- url     : https://prove2.me/theorems/6eb85b89-affc-5834-a52c-1b9af025ce62
-- title:
--   Oriented Branch: edge leaving vertices eq boundary
-- statement:
--   Any tree edge leaving an oriented branch is exactly its deleted boundary
--   edge.  Every other adjacent edge survives in the deleted graph and therefore
--   keeps both endpoints in the same connected component.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L192-L205
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L192-L205

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.edge_leaving_vertices_eq_boundary (B : OrientedBranch T)
    {u v : V} (hu : u ∈ B.vertices) (hv : v ∉ B.vertices)
    (huv : T.graph.Adj u v) :
    s(u, v) = s(B.root, B.parent) := by sorry
