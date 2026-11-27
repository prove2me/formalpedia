-- Prove2me | Theorems.Thm_TreeStack_F_eq_neg_odd_iff
-- name    : TreeStack.F_eq_neg_odd_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:11:32.740799+00:00
-- url     : https://prove2.me/theorems/95a255cc-26a3-429e-b707-72084f48b6af
-- title:
--   Tree Stack: F eq neg odd iff
-- statement:
--   Negative outputs are precisely the negative odd integers, with their
--   preimages written in the form used by the branch induction.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L63-L66
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L63-L66

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
set_option autoImplicit false
open TreeStack

theorem TreeStack.F_eq_neg_odd_iff {z r : ℤ} (hr : 0 ≤ r) :
    F z = -(2 * r + 1) ↔ z = 1 - r := by sorry
