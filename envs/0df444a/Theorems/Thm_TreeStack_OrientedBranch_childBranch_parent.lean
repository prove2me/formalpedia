-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
-- name    : TreeStack.OrientedBranch.childBranch_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:08:57.154062+00:00
-- url     : https://prove2.me/theorems/e85d9bb4-fc66-43af-865d-97b5e7363d5c
-- title:
--   Oriented Branch: child Branch parent
-- statement:
--   The Oriented Branch construction uses the child Branch parent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L114-L115
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L114-L115

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.childBranch_parent (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).parent = B.root := by sorry

attribute [defeq] TreeStack.OrientedBranch.childBranch_parent
