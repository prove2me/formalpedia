-- Prove2me | Theorems.Thm_TwoBQO_subtype
-- name    : TwoBQO.subtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:46.405202+00:00
-- url     : https://prove2.me/theorems/46be1b28-f825-4a18-8fb2-915f0a9ab73d
-- title:
--   Two BQO: subtype
-- statement:
--   **Subtype closure.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L181-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L181-L183

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

theorem TwoBQO.subtype {α : Type*} {r : α → α → Prop} (h : TwoBQO r) (p : α → Prop) :
    TwoBQO fun a b : Subtype p => r a.val b.val := by sorry
