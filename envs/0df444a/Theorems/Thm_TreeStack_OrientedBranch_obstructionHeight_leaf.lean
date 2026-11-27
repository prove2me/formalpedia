-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_obstructionHeight_leaf
-- name    : TreeStack.OrientedBranch.obstructionHeight_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:46:07.786915+00:00
-- url     : https://prove2.me/theorems/5826fd3b-c3d6-4244-8dfe-9d4c29e121cd
-- title:
--   Oriented Branch: obstruction Height leaf
-- statement:
--   The Oriented Branch construction uses the obstruction Height leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L110-L114
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L110-L114

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.obstructionHeight_leaf (B : OrientedBranch T)
    (hLeaf : T.graph.degree B.root = 1) :
    obstructionHeight B = 1 := by sorry
