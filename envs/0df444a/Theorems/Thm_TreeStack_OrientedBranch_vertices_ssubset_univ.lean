-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_vertices_ssubset_univ
-- name    : TreeStack.OrientedBranch.vertices_ssubset_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:09:53.921503+00:00
-- url     : https://prove2.me/theorems/1cc577ca-dd43-584e-892c-e9161374bcb0
-- title:
--   Oriented Branch: vertices ssubset univ
-- statement:
--   The branch is a proper subset of the whole finite vertex set.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L75-L79
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L75-L79

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.vertices_ssubset_univ (B : OrientedBranch T) :
    B.vertices ⊂ (Finset.univ : Finset V) := by sorry
