-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_obstructionHeight_pos
-- name    : TreeStack.OrientedBranch.obstructionHeight_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:49:04.288834+00:00
-- url     : https://prove2.me/theorems/ff34ff61-dbc0-56ce-9691-2fb1eed4d13f
-- title:
--   Oriented Branch: obstruction Height pos
-- statement:
--   The Oriented Branch construction uses the obstruction Height pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L132-L135
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L132-L135

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.obstructionHeight_pos (B : OrientedBranch T) :
    0 < obstructionHeight B := by sorry
