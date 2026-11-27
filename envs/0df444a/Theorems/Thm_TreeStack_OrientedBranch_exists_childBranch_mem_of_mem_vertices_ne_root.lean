-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_exists_childBranch_mem_of_mem_vertices_ne_root
-- name    : TreeStack.OrientedBranch.exists_childBranch_mem_of_mem_vertices_ne_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:13:15.918594+00:00
-- url     : https://prove2.me/theorems/3a61edfd-3e3e-4da5-941e-3496037e34ed
-- title:
--   Oriented Branch: exists child Branch mem of mem vertices ne root
-- statement:
--   Every non-root vertex of an oriented branch lies in one of the genuine
--   child branches at the branch root.  This is the existence half of the child
--   decomposition used by the constructive boundary induction; sibling
--   disjointness supplies uniqueness.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L224-L277
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L224-L277

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.exists_childBranch_mem_of_mem_vertices_ne_root
    (B : OrientedBranch T) {x : V}
    (hx : x ∈ B.vertices) (hxr : x ≠ B.root) :
    ∃ c : B.Child, x ∈ (B.childBranch c).vertices := by sorry
