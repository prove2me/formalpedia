-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_defectiveSupportEdge_reverse_iff
-- name    : TreeStack.OrientedBranch.defectiveSupportEdge_reverse_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:48:26.825851+00:00
-- url     : https://prove2.me/theorems/43977ba6-f5f9-45c7-9549-a5e7ce33c2cb
-- title:
--   Oriented Branch: defective Support Edge reverse iff
-- statement:
--   The Oriented Branch construction uses the defective Support Edge reverse iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L349-L355
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L349-L355

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.defectiveSupportEdge_reverse_iff
    (C : Configuration V) (B : OrientedBranch T) :
    B.reverseBranch.DefectiveSupportEdge C ↔
      B.DefectiveSupportEdge C := by sorry
