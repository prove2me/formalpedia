-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_eq_root_of_mem_vertices_adj_parent
-- name    : TreeStack.OrientedBranch.eq_root_of_mem_vertices_adj_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:13:00.208962+00:00
-- url     : https://prove2.me/theorems/e9b0af48-3529-4df7-8a29-b74d080c5096
-- title:
--   Oriented Branch: eq root of mem vertices adj parent
-- statement:
--   The external boundary vertex has no neighbor inside the branch other than
--   the branch root.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L209-L217
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L209-L217

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.eq_root_of_mem_vertices_adj_parent (B : OrientedBranch T)
    {u : V} (hu : u ∈ B.vertices) (hup : T.graph.Adj u B.parent) :
    u = B.root := by sorry
