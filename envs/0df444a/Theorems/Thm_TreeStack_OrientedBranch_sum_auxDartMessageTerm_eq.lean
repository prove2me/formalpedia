-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_sum_auxDartMessageTerm_eq
-- name    : TreeStack.OrientedBranch.sum_auxDartMessageTerm_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:15:56.089083+00:00
-- url     : https://prove2.me/theorems/b386a757-b08f-4c99-8518-bf72ea903087
-- title:
--   Oriented Branch: sum aux Dart Message Term eq
-- statement:
--   Summing directed message terms by their head recovers the weighted rooted
--   message sums.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L309-L335
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L309-L335

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.sum_auxDartMessageTerm_eq
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ d : T.graph.Dart,
      auxDartMessageTerm C ambientRoot hScores d) =
      ∑ v : V,
        auxWeightInt C ambientRoot hScores v * rootMessageSum T C v := by sorry
