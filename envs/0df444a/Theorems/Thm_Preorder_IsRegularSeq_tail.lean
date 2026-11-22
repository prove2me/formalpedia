-- Prove2me | Theorems.Thm_Preorder_IsRegularSeq_tail
-- name    : Preorder.IsRegularSeq.tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:08.636936+00:00
-- url     : https://prove2.me/theorems/96339bde-d158-48e1-a41f-e4799da94167
-- title:
--   Is Regular Seq: tail
-- statement:
--   A tail of a regular sequence is regular.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Regular.lean#L62-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Regular.lean#L62-L70

module
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Order.WellFoundedSet
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
open Preorder

theorem Preorder.IsRegularSeq.tail {Q : Type*} {r : Q → Q → Prop}
    {f : ℕ → Q} (hf : IsRegularSeq r f) (k : ℕ) :
    IsRegularSeq r fun i => f (i + k) := by sorry
