-- Prove2me | Theorems.Thm_TreeStack_incidentBranch_vertices_disjoint
-- name    : TreeStack.incidentBranch_vertices_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:34:54.035796+00:00
-- url     : https://prove2.me/theorems/8ce9d953-8a96-5109-817c-a8edabb58b22
-- title:
--   Tree Stack: incident Branch vertices disjoint
-- statement:
--   Distinct incident branches at one target have disjoint interiors.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L24-L96
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L24-L96

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.incidentBranch_vertices_disjoint
    (r : V) {u v : V}
    (hu : T.graph.Adj u r) (hv : T.graph.Adj v r)
    (huv : u ≠ v) :
    Disjoint
      (incidentBranch T r u hu).vertices
      (incidentBranch T r v hv).vertices := by sorry
