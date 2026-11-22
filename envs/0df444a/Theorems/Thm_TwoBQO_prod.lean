-- Prove2me | Theorems.Thm_TwoBQO_prod
-- name    : TwoBQO.prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:25.692105+00:00
-- url     : https://prove2.me/theorems/962db935-1447-415e-a548-41c3f1e21d73
-- title:
--   Two BQO: prod
-- statement:
--   **Product closure** (Dickson's lemma for 2-BQO). If `r` on `α` and `s` on `β` are 2-BQO,
--   then the componentwise product `fun (a₁,b₁) (a₂,b₂) => r a₁ a₂ ∧ s b₁ b₂` on `α × β` is
--   2-BQO.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L230-L244
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L230-L244

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

theorem TwoBQO.prod {α β : Type*} {r : α → α → Prop} {s : β → β → Prop} (hr : TwoBQO r)
    (hs : TwoBQO s) : TwoBQO fun x y : α × β => r x.1 y.1 ∧ s x.2 y.2 := by sorry
