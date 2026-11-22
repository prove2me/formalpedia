-- Prove2me | Theorems.Thm_TwoBQO_of_finite_coloring
-- name    : TwoBQO.of_finite_coloring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:33.654516+00:00
-- url     : https://prove2.me/theorems/c0dc2abc-de25-4f87-8d92-9cb7bb78ed2e
-- title:
--   Two BQO: of finite coloring
-- statement:
--   **A preorder with a finite partial order quotient is 2-BQO.** If `c : α → κ` with `κ`
--   finite and *same colour ⟹ `r`-related*, then `r` is 2-BQO: colour pairs by `c (f m n)`,
--   Ramsey-for-pairs (`infinite_ramsey_pairs`) makes the restriction monochromatic, so any triple is
--   good. In particular, if `r` is a preorder whose induced partial order on `r`-equivalence classes
--   has finitely many classes, taking `c` to be the quotient map gives `TwoBQO r`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L139-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L139-L144

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

theorem TwoBQO.of_finite_coloring {α κ : Type*} [Finite κ] (r : α → α → Prop) (c : α → κ)
    (hc : ∀ a b, c a = c b → r a b) : TwoBQO r := by sorry
