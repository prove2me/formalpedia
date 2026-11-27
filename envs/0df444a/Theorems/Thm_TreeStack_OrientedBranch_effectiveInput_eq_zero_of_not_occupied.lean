-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_effectiveInput_eq_zero_of_not_occupied
-- name    : TreeStack.OrientedBranch.effectiveInput_eq_zero_of_not_occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:50:59.639323+00:00
-- url     : https://prove2.me/theorems/c6fc2228-ca6a-4bc1-a752-d2ac50d60db4
-- title:
--   Oriented Branch: effective Input eq zero of not occupied
-- statement:
--   If an oriented branch is configuration-empty, its effective input is zero.
--   This does not identify the branch message with integer zero: its message is
--   still the separate value \`EMPTY\`.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L812-L841
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L812-L841

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.effectiveInput_eq_zero_of_not_occupied
    (C : Configuration V) (B : OrientedBranch T)
    (hEmpty : ¬ B.Occupied C) :
    B.effectiveInput C = 0 := by sorry
