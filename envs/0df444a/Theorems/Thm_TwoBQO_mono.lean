-- Prove2me | Theorems.Thm_TwoBQO_mono
-- name    : TwoBQO.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:46.058855+00:00
-- url     : https://prove2.me/theorems/faac5462-9313-4aed-8bf1-02d1758c646e
-- title:
--   Two BQO: mono
-- statement:
--   The Two BQO construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L185-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L185-L189

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

theorem TwoBQO.mono {α : Type*} {r s : α → α → Prop} (h : TwoBQO r)
    (hincl : ∀ a b, r a b → s a b) : TwoBQO s := by sorry
