-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_childEdge_ne_boundary
-- name    : TreeStack.OrientedBranch.childEdge_ne_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:10:13.132907+00:00
-- url     : https://prove2.me/theorems/6072b7d1-fdaa-45a0-945c-bae91463004c
-- title:
--   Oriented Branch: child Edge ne boundary
-- statement:
--   The child edge differs from the boundary edge of its parent branch.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L118-L124
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L118-L124

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.childEdge_ne_boundary (B : OrientedBranch T) (c : B.Child) :
    s(B.root, c.vertex) ≠ s(B.root, B.parent) := by sorry
