-- Prove2me | Theorems.Thm_TwoBQO_dom_twoBQO
-- name    : TwoBQO.dom_twoBQO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:36.531811+00:00
-- url     : https://prove2.me/theorems/4ec21f6a-60e9-492c-b29b-687a07efc9ca
-- title:
--   Two BQO: dom two BQO
-- statement:
--   **The domination order on subsets of a 2-BQO is WQO.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L402-L409
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L402-L409

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

theorem TwoBQO.dom_twoBQO {α : Type*} {r : α → α → Prop} (hr : TwoBQO r) :
    WellQuasiOrdered (DomOrder r) := by sorry
