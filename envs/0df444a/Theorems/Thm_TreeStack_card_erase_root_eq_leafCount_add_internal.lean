-- Prove2me | Theorems.Thm_TreeStack_card_erase_root_eq_leafCount_add_internal
-- name    : TreeStack.card_erase_root_eq_leafCount_add_internal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:17.228337+00:00
-- url     : https://prove2.me/theorems/683423c6-4070-4755-9877-ee27330b1ab9
-- title:
--   Tree Stack: card erase root eq leaf Count add internal
-- statement:
--   The Tree Stack construction uses the card erase root eq leaf Count add internal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L106-L113
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L106-L113

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical

theorem TreeStack.card_erase_root_eq_leafCount_add_internal {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V)
    (hdeg : ∀ v, 0 < T.graph.degree v) :
    ((Finset.univ : Finset V).erase r).card =
      leafCount T r + (nonRootInternalVertices T r).card := by sorry
