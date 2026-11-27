-- Prove2me | Theorems.Thm_TreeStack_F_eq_nonneg_iff
-- name    : TreeStack.F_eq_nonneg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:11:37.444296+00:00
-- url     : https://prove2.me/theorems/8d11adc1-55ad-4201-a2be-b582e4583777
-- title:
--   Tree Stack: F eq nonneg iff
-- statement:
--   For a nonnegative target transfer value `k`, the two generic preimages
--   are `2k` and `2k+3`; the first disappears at `k=0`.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L70-L73
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean#L70-L73

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
set_option autoImplicit false
open TreeStack

theorem TreeStack.F_eq_nonneg_iff {z k : ℤ} (hk : 0 ≤ k) :
    F z = k ↔ (0 < k ∧ z = 2 * k) ∨ z = 2 * k + 3 := by sorry
