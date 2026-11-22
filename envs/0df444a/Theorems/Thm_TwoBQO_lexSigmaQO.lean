-- Prove2me | Theorems.Thm_TwoBQO_lexSigmaQO
-- name    : TwoBQO.lexSigmaQO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:49.688264+00:00
-- url     : https://prove2.me/theorems/cdab6e6b-2638-42f5-86b7-4a7bd1bf5b8d
-- title:
--   Two BQO: lex Sigma QO
-- statement:
--   **Sum theorem for 2-BQO along a quasi-order.** If `r` on `ι` is 2-BQO and each `t i` on
--   `s i` is 2-BQO, then `Σ i, s i` with `LexSumRelQO r s t` is 2-BQO.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L365-L371
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L365-L371

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
variable {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*) (t : ∀ i, s i → s i → Prop)

theorem TwoBQO.lexSigmaQO {ι : Type*} (r : ι → ι → Prop) (hr : TwoBQO r) (s : ι → Type*)
    (t : ∀ i, s i → s i → Prop) (ht : ∀ i, TwoBQO (t i)) : TwoBQO (TwoBQO.LexSumRelQO r s t) := by sorry
