-- Prove2me | Theorems.Thm_P2M_WellQuasiOrdered_sublistForall__eefc84a6e857
-- name    : P2M_WellQuasiOrdered_sublistForall__eefc84a6e857
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:51.586766+00:00
-- url     : https://prove2.me/theorems/62a8d20c-33e6-46b1-b4a5-444b11184e3a
-- title:
--   P2 M Well Quasi Ordered sublist Forall  eefc84a6e857: P2 M Well Quasi Ordered sublist Forall  eefc84a6e857
-- statement:
--   **Higman's Lemma, unrestricted.** If `r` is a WQO on `Q`, then `List.SublistForall₂ r` is a
--   WQO on all of `List Q` (not just on a `PartiallyWellOrderedOn` subset). A direct restatement of
--   `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂` via
--   `partiallyWellOrderedOn_univ_iff`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Regular.lean#L173-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Regular.lean#L173-L176

module
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Order.WellFoundedSet
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section

theorem P2M_WellQuasiOrdered_sublistForall__eefc84a6e857 {Q : Type*} {r : Q → Q → Prop} [IsPreorder Q r]
    (h : WellQuasiOrdered r) : WellQuasiOrdered (List.SublistForall₂ r) := by sorry

alias «WellQuasiOrdered».«sublistForall₂» := P2M_WellQuasiOrdered_sublistForall__eefc84a6e857
