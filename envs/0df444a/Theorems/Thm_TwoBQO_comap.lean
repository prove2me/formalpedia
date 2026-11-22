-- Prove2me | Theorems.Thm_TwoBQO_comap
-- name    : TwoBQO.comap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:22.343049+00:00
-- url     : https://prove2.me/theorems/4e7492a9-f709-4a74-8713-0179074457f6
-- title:
--   Two BQO: comap
-- statement:
--   2-BQO is closed under monotone preimage: if `φ : β → α` is monotone and `r` on `α` is
--   2-BQO, then the pullback of `r` along `φ` is 2-BQO.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L174-L178
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L174-L178

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

theorem TwoBQO.comap {α β : Type*} {r : α → α → Prop} (h : TwoBQO r) (φ : β → α) :
    TwoBQO fun a b => r (φ a) (φ b) := by sorry
