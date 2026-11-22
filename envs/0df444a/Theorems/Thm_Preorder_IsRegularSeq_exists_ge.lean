-- Prove2me | Theorems.Thm_Preorder_IsRegularSeq_exists_ge
-- name    : Preorder.IsRegularSeq.exists_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:11.132212+00:00
-- url     : https://prove2.me/theorems/2a3d7f37-eff3-4103-a7e9-e791f7854ecb
-- title:
--   Is Regular Seq: exists ge
-- statement:
--   A regular sequence has arbitrarily large indices dominating any given index:
--   for every `i` and threshold `N` there is `j ≥ N` with `f i ≤ f j`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Regular.lean#L55-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Regular.lean#L55-L59

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

theorem Preorder.IsRegularSeq.exists_ge {Q : Type*} {r : Q → Q → Prop}
    {f : ℕ → Q} (hf : IsRegularSeq r f) (i N : ℕ) :
    ∃ j, N ≤ j ∧ r (f i) (f j) := by sorry
