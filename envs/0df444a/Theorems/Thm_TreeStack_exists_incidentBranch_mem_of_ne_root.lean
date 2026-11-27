-- Prove2me | Theorems.Thm_TreeStack_exists_incidentBranch_mem_of_ne_root
-- name    : TreeStack.exists_incidentBranch_mem_of_ne_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:35:01.522017+00:00
-- url     : https://prove2.me/theorems/8a4a74e8-fd9a-5831-ae6c-cdccfe248bbb
-- title:
--   Tree Stack: exists incident Branch mem of ne root
-- statement:
--   Every vertex other than the target lies in a genuine incident branch.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L119-L152
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L119-L152

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.exists_incidentBranch_mem_of_ne_root
    (r : V) {x : V} (hxr : x ≠ r) :
    ∃ u : V, ∃ h : T.graph.Adj u r,
      x ∈ (incidentBranch T r u h).vertices := by sorry
