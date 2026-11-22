-- Prove2me | Theorems.Thm_TwoBQO_union
-- name    : TwoBQO.union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:47.790122+00:00
-- url     : https://prove2.me/theorems/90786748-a9af-42f6-a911-73f71510f05b
-- title:
--   Two BQO: union
-- statement:
--   **Union of two 2-BQO parts is 2-BQO.** If `p, q` cover `α` and `r` is 2-BQO on each
--   sub-part `{x // p x}` and `{x // q x}`, then `r` is 2-BQO on `α`.
--
--   2-colour each pair `(m,n)` by whether `p (f m n)` holds; Ramsey-for-pairs gives an infinite
--   restriction landing wholly in one part, where the corresponding 2-BQO supplies a good triple.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L204-L221
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L204-L221

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

theorem TwoBQO.union {α : Type*} (r : α → α → Prop) (p q : α → Prop) (hcover : ∀ a, p a ∨ q a)
    (hp : TwoBQO (fun a b : {x : α // p x} => r a.val b.val))
    (hq : TwoBQO (fun a b : {x : α // q x} => r a.val b.val)) :
    TwoBQO r := by sorry
