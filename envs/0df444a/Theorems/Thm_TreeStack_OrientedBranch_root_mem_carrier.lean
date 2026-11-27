-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
-- name    : TreeStack.OrientedBranch.root_mem_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:26:36.844129+00:00
-- url     : https://prove2.me/theorems/d52fd00b-39be-4f98-aca3-08f55692388f
-- title:
--   Oriented Branch: root mem carrier
-- statement:
--   The Oriented Branch construction uses the root mem carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L395-L398
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L395-L398

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.root_mem_carrier (B : OrientedBranch T) :
    B.root ∈ B.carrier := by sorry
