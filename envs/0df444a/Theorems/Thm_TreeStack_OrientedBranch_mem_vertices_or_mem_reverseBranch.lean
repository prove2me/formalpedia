-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_mem_vertices_or_mem_reverseBranch
-- name    : TreeStack.OrientedBranch.mem_vertices_or_mem_reverseBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:48:56.762797+00:00
-- url     : https://prove2.me/theorems/2e87a2b2-945e-5ae1-8fb8-eb94f6177af9
-- title:
--   Oriented Branch: mem vertices or mem reverse Branch
-- statement:
--   Every vertex lies on one of the two sides of an oriented tree edge.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L46-L66
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L46-L66

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.mem_vertices_or_mem_reverseBranch
    (B : OrientedBranch T) (x : V) :
    x ∈ B.vertices ∨ x ∈ B.reverseBranch.vertices := by sorry
