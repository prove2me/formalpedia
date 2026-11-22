-- Prove2me | Theorems.Thm_TwoBQO_pi
-- name    : TwoBQO.pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:29.680546+00:00
-- url     : https://prove2.me/theorems/8cefada0-067f-4710-9e2c-7c6184d60761
-- title:
--   Two BQO: pi
-- statement:
--   **Iterated finite product.** For a `Fintype` index `ι`, the product `∀ i, α i` with pointwise
--   quasi-order is 2-BQO when each component is.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L248-L266
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L248-L266

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

theorem TwoBQO.pi : ∀ (n : ℕ) (α : Fin n → Type*) (r : ∀ i : Fin n, α i → α i → Prop),
    (∀ i, TwoBQO (r i)) → TwoBQO fun f g : ∀ i, α i => ∀ i, r i (f i) (g i) := by sorry
