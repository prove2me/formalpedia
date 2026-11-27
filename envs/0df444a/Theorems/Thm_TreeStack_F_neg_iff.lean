-- Prove2me | Theorems.Thm_TreeStack_F_neg_iff
-- name    : TreeStack.F_neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:11:01.335915+00:00
-- url     : https://prove2.me/theorems/06e25bdb-ffa5-4061-a03d-465229179aab
-- title:
--   Tree Stack: F neg iff
-- statement:
--   The transfer is negative exactly on inputs at most one.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L52-L54
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L52-L54

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
set_option autoImplicit false
open TreeStack

theorem TreeStack.F_neg_iff (z : ℤ) : F z < 0 ↔ z ≤ 1 := by sorry
