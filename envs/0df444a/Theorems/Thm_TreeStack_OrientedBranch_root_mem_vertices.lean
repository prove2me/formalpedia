-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
-- name    : TreeStack.OrientedBranch.root_mem_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:08:35.409716+00:00
-- url     : https://prove2.me/theorems/91f5a908-3cac-4064-bc68-30c0a292d0aa
-- title:
--   Oriented Branch: root mem vertices
-- statement:
--   The Oriented Branch construction uses the root mem vertices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L39-L43
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L39-L43

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.root_mem_vertices (B : OrientedBranch T) :
    B.root ∈ B.vertices := by sorry
