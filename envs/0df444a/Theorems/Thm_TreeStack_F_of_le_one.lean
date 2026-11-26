-- Prove2me | Theorems.Thm_TreeStack_F_of_le_one
-- name    : TreeStack.F_of_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:09:28.553923+00:00
-- url     : https://prove2.me/theorems/dba3061f-ee40-5338-a9f4-a8b0f3f726ee
-- title:
--   Tree Stack: F of le one
-- statement:
--   The Tree Stack construction uses the F of le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L27-L28
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L27-L28

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
set_option autoImplicit false
open TreeStack

theorem TreeStack.F_of_le_one {x : ℤ} (h : x ≤ 1) : F x = 2 * x - 3 := by sorry
