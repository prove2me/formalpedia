-- Prove2me | Theorems.Thm_TreeStack_not_stackable_oneOn_of_two_le_card
-- name    : TreeStack.not_stackable_oneOn_of_two_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:44.794665+00:00
-- url     : https://prove2.me/theorems/b991271c-543a-432b-8586-f5c350b1b4ed
-- title:
--   Tree Stack: not stackable one On of two le card
-- statement:
--   The Tree Stack construction uses the not stackable one On of two le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L90-L112
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L90-L112

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
set_option autoImplicit false
open TreeStack

theorem TreeStack.not_stackable_oneOn_of_two_le_card {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {s : Finset V} (hs : 2 ≤ s.card) :
    ¬ Stackable G (oneOn s) := by sorry
