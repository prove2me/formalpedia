-- Prove2me | Theorems.Thm_TreeStack_mem_incidentBranch_vertices_not_mem_sibling_carrier
-- name    : TreeStack.mem_incidentBranch_vertices_not_mem_sibling_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:57.039531+00:00
-- url     : https://prove2.me/theorems/50d6ce5f-0330-56ef-ad8a-d5e40c1a0693
-- title:
--   Tree Stack: mem incident Branch vertices not mem sibling carrier
-- statement:
--   A vertex inside one incident branch is outside every distinct incident
--   branch carrier.  The only shared carrier point is the target itself.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L100-L116
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L100-L116

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.mem_incidentBranch_vertices_not_mem_sibling_carrier
    (r : V) {u v w : V}
    (hu : T.graph.Adj u r) (hv : T.graph.Adj v r)
    (huv : u ≠ v)
    (hw : w ∈ (incidentBranch T r u hu).vertices) :
    w ∉ (incidentBranch T r v hv).carrier := by sorry
