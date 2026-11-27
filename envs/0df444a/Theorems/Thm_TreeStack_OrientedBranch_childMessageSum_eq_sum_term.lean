-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_childMessageSum_eq_sum_term
-- name    : TreeStack.OrientedBranch.childMessageSum_eq_sum_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:32:43.40716+00:00
-- url     : https://prove2.me/theorems/09a5b83f-fa83-5b61-a49e-aafef10ece2e
-- title:
--   Oriented Branch: child Message Sum eq sum term
-- statement:
--   The Oriented Branch construction uses the child Message Sum eq sum term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L852-L860
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L852-L860

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

theorem TreeStack.OrientedBranch.childMessageSum_eq_sum_term
    (B : OrientedBranch T) (C : Configuration V) :
    childMessageSum C B = ∑ v : V, B.childMessageTerm C v := by sorry
