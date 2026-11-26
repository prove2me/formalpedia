-- Prove2me | Theorems.Thm_TreeStack_F_of_ge_five_odd
-- name    : TreeStack.F_of_ge_five_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:09:51.272987+00:00
-- url     : https://prove2.me/theorems/27fb6d06-6d5e-5da0-b75f-f70e6d828724
-- title:
--   Tree Stack: F of ge five odd
-- statement:
--   The Tree Stack construction uses the F of ge five odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L41-L44
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L41-L44

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
set_option autoImplicit false
open TreeStack

theorem TreeStack.F_of_ge_five_odd {x : ℤ} (h5 : 5 ≤ x) (ho : x % 2 ≠ 0) :
    F x = (x - 3) / 2 := by sorry
