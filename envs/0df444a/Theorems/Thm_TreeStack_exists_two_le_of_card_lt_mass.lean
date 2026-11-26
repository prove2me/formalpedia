-- Prove2me | Theorems.Thm_TreeStack_exists_two_le_of_card_lt_mass
-- name    : TreeStack.exists_two_le_of_card_lt_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:53.106502+00:00
-- url     : https://prove2.me/theorems/5bfbf1d2-77fd-4e5f-b1c5-8c562515be36
-- title:
--   Tree Stack: exists two le of card lt mass
-- statement:
--   If the total mass exceeds the vertex count, some vertex carries at least
--   two pebbles.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L130-L142
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L130-L142

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
set_option autoImplicit false
open TreeStack

theorem TreeStack.exists_two_le_of_card_lt_mass {V : Type*} [Fintype V]
    (C : Configuration V) (h : Fintype.card V < mass C) :
    ∃ v, 2 ≤ C v := by sorry
