-- Prove2me | Theorems.Thm_TreeStack_RootTask_mem_vertices_not_mem_sibling_carrier
-- name    : TreeStack.RootTask.mem_vertices_not_mem_sibling_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:35:28.992533+00:00
-- url     : https://prove2.me/theorems/8d6fb74e-1dae-5fd0-a0a5-a6a2e26817b1
-- title:
--   Root Task: mem vertices not mem sibling carrier
-- statement:
--   A vertex in one rooted task interior lies outside the carrier of every
--   distinct rooted task.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L334-L344
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L334-L344

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.RootTask.mem_vertices_not_mem_sibling_carrier
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (s t : RootTask T C r) (hst : s.1 ≠ t.1) {v : V}
    (hv : v ∈ s.branch.vertices) :
    v ∉ t.branch.carrier := by sorry
