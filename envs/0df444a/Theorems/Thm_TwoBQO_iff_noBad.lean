-- Prove2me | Theorems.Thm_TwoBQO_iff_noBad
-- name    : TwoBQO.iff_noBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:23.577083+00:00
-- url     : https://prove2.me/theorems/be5c710b-0b71-435a-86fa-fd5f11b2bcb3
-- title:
--   Two BQO: iff no Bad
-- statement:
--   The Two BQO construction uses the iff no Bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L115-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L115-L117

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

theorem TwoBQO.iff_noBad {α : Type*} (r : α → α → Prop) : TwoBQO r ↔ TwoBQON r := by sorry
