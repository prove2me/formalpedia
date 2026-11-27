-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_sum_edgeSeparatedCharge_le_auxDefectBudget
-- name    : TreeStack.OrientedBranch.sum_edgeSeparatedCharge_le_auxDefectBudget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:13:55.576086+00:00
-- url     : https://prove2.me/theorems/006c6322-04b9-4291-9078-38e82aaaec06
-- title:
--   Oriented Branch: sum edge Separated Charge le aux Defect Budget
-- statement:
--   The total separated charge is bounded by the available weighted vertex
--   defect budget.  Injectivity is used only after retained-defect and
--   nonretained-`EMPTY` charges have been distinguished.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L159-L174
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L159-L174

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.sum_edgeSeparatedCharge_le_auxDefectBudget
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      edgeSeparatedCharge C ambientRoot hScores e) ≤
      auxDefectBudget C ambientRoot hScores := by sorry
