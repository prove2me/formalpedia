-- Prove2me | Theorems.Thm_TreeStack_F_eq_zero_iff
-- name    : TreeStack.F_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:11:04.944022+00:00
-- url     : https://prove2.me/theorems/71012b52-3749-4877-accd-566ef1b043fa
-- title:
--   Tree Stack: F eq zero iff
-- statement:
--   Zero is an exceptional transfer value: it has the unique preimage three.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L57-L59
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L57-L59

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
set_option autoImplicit false
open TreeStack

theorem TreeStack.F_eq_zero_iff (z : ℤ) : F z = 0 ↔ z = 3 := by sorry
