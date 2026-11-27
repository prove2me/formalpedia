-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_Child_eq_of_vertex_eq
-- name    : TreeStack.OrientedBranch.Child.eq_of_vertex_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:12:32.975547+00:00
-- url     : https://prove2.me/theorems/0b246419-3947-5894-8a67-9229a711337c
-- title:
--   Child: eq of vertex eq
-- statement:
--   A child choice is determined by its vertex; the remaining fields are
--   propositions and hence proof-irrelevant.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L95-L103
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L95-L103

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.Child.eq_of_vertex_eq {B : OrientedBranch T} {c d : B.Child}
    (h : c.vertex = d.vertex) : c = d := by sorry
