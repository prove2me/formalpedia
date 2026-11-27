-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_card_childFinset_add_one
-- name    : TreeStack.OrientedBranch.card_childFinset_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:51:04.961625+00:00
-- url     : https://prove2.me/theorems/bc37182d-a7fe-4339-882a-f5568a76c2d7
-- title:
--   Oriented Branch: card child Finset add one
-- statement:
--   The Oriented Branch construction uses the card child Finset add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L436-L442
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L436-L442

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.card_childFinset_add_one (B : OrientedBranch T) :
    B.childFinset.card + 1 = T.graph.degree B.root := by sorry
