-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_supportEdge_reverse_iff
-- name    : TreeStack.OrientedBranch.supportEdge_reverse_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:48:14.178798+00:00
-- url     : https://prove2.me/theorems/ef6f5430-89fe-51d6-bcf2-aff917aee323
-- title:
--   Oriented Branch: support Edge reverse iff
-- statement:
--   The Oriented Branch construction uses the support Edge reverse iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L92-L95
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L92-L95

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.supportEdge_reverse_iff
    (C : Configuration V) (B : OrientedBranch T) :
    B.reverseBranch.SupportEdge C ↔ B.SupportEdge C := by sorry
