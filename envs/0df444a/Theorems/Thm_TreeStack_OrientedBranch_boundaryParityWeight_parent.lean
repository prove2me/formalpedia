-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
-- name    : TreeStack.OrientedBranch.boundaryParityWeight_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:26:50.318081+00:00
-- url     : https://prove2.me/theorems/bc04c1d7-c999-4637-9860-232a014c5303
-- title:
--   Oriented Branch: boundary Parity Weight parent
-- statement:
--   The Oriented Branch construction uses the boundary Parity Weight parent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1779-L1781
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1779-L1781

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]

theorem TreeStack.OrientedBranch.boundaryParityWeight_parent (B : OrientedBranch T) :
    B.boundaryParityWeight B.parent = 1 := by sorry
