-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
-- name    : TreeStack.OrientedBranch.parent_mem_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:26:03.270642+00:00
-- url     : https://prove2.me/theorems/b12aaf8a-b4d8-53fc-911f-90363600567c
-- title:
--   Oriented Branch: parent mem carrier
-- statement:
--   The Oriented Branch construction uses the parent mem carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L400-L403
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L400-L403

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.parent_mem_carrier (B : OrientedBranch T) :
    B.parent ∈ B.carrier := by sorry
