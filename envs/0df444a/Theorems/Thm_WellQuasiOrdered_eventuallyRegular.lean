-- Prove2me | Theorems.Thm_WellQuasiOrdered_eventuallyRegular
-- name    : WellQuasiOrdered.eventuallyRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:50.386365+00:00
-- url     : https://prove2.me/theorems/cb93e05b-bee0-415e-aa70-0ace1a859a4d
-- title:
--   Well Quasi Ordered: eventually Regular
-- statement:
--   **In a WQO every sequence is eventually regular.** In fact this is an equivalent
--   characterization of WQO, since any bad sequence admits no regular tail.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Regular.lean#L134-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Regular.lean#L134-L142

module
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Order.WellFoundedSet
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section

theorem WellQuasiOrdered.eventuallyRegular {Q : Type*} (r : Q → Q → Prop)
    (hwqo : WellQuasiOrdered r) (f : ℕ → Q) :
    ∃ n : ℕ, IsRegularSeq r fun i => f (i + n) := by sorry
