-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_no_auxArrow_to_root_of_not_occupied
-- name    : TreeStack.OrientedBranch.no_auxArrow_to_root_of_not_occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:07:26.173977+00:00
-- url     : https://prove2.me/theorems/473b2854-0e70-5560-9db2-86b1b730a81b
-- title:
--   Oriented Branch: no aux Arrow to root of not occupied
-- statement:
--   No auxiliary arrow can enter the root of a configuration-empty oriented
--   branch.  An arrow across the boundary would retain the empty side, while an
--   arrow from a genuine child would retain an occupied subbranch inside it.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L205-L229
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L205-L229

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.no_auxArrow_to_root_of_not_occupied
    (C : Configuration V) (ambientRoot : V)
    (B : OrientedBranch T) (hEmpty : ¬ B.Occupied C) (u : V) :
    ¬ AuxArrow (T := T) C ambientRoot u B.root := by sorry
