-- Prove2me | Theorems.Thm_TwoBQO_wellQuasiOrdered
-- name    : TwoBQO.wellQuasiOrdered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:30.267223+00:00
-- url     : https://prove2.me/theorems/9e105f85-0c2f-47ec-b0f4-d0cc89f6453d
-- title:
--   Two BQO: well Quasi Ordered
-- statement:
--   **2-BQO implies WQO.** Given a sequence `g : ℕ → α`, apply 2-BQO to the pair-sequence
--   `(m, n, _) ↦ g m`. A good triple `m < n < l` yields `r (g m) (g n)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L125-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L125-L128

module
public import Mathlib.SetTheory.Ordinal.Basic
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_NashWilliams_Order_TwoBQO
set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section

theorem TwoBQO.wellQuasiOrdered {α : Type*} {r : α → α → Prop} (h : TwoBQO r) :
    WellQuasiOrdered r := by sorry
