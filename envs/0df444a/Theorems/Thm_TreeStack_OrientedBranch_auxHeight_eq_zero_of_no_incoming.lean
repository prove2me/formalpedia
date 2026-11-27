-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxHeight_eq_zero_of_no_incoming
-- name    : TreeStack.OrientedBranch.auxHeight_eq_zero_of_no_incoming
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:07:21.916857+00:00
-- url     : https://prove2.me/theorems/fe96aac5-9046-5345-8f2a-d9ce590fc8f3
-- title:
--   Oriented Branch: aux Height eq zero of no incoming
-- statement:
--   A vertex with no incoming auxiliary arrow has auxiliary height zero.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L419-L426
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L419-L426

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxHeight_eq_zero_of_no_incoming
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V)
    (hNo : ∀ u, ¬ AuxArrow (T := T) C ambientRoot u v) :
    auxHeight C ambientRoot hScores v = 0 := by sorry
