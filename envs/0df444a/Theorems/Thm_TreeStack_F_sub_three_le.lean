-- Prove2me | Theorems.Thm_TreeStack_F_sub_three_le
-- name    : TreeStack.F_sub_three_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:10:59.497873+00:00
-- url     : https://prove2.me/theorems/51ce5598-6b7c-4abd-b2a3-576e72f35a92
-- title:
--   Tree Stack: F sub three le
-- statement:
--   Lowering an effective input by three cannot increase the transfer.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L47-L49
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L47-L49

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
set_option autoImplicit false
open TreeStack

theorem TreeStack.F_sub_three_le (z : ℤ) : F (z - 3) ≤ F z := by sorry
