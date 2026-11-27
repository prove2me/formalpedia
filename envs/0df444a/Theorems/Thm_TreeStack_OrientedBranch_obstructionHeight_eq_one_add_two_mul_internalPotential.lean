-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_obstructionHeight_eq_one_add_two_mul_internalPotential
-- name    : TreeStack.OrientedBranch.obstructionHeight_eq_one_add_two_mul_internalPotential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:51:03.934813+00:00
-- url     : https://prove2.me/theorems/baf5722d-5bb4-53cf-abf3-340782961867
-- title:
--   Oriented Branch: obstruction Height eq one add two mul internal Potential
-- statement:
--   Closed form for the recursive obstruction height.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L490-L648
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L490-L648

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.obstructionHeight_eq_one_add_two_mul_internalPotential
    (B : OrientedBranch T) :
    B.obstructionHeight = 1 + 2 * B.internalPotential := by sorry
