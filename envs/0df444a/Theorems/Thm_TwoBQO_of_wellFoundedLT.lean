-- Prove2me | Theorems.Thm_TwoBQO_of_wellFoundedLT
-- name    : TwoBQO.of_wellFoundedLT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:20.608519+00:00
-- url     : https://prove2.me/theorems/8f6703ed-2180-442a-a177-c4be6bc1b055
-- title:
--   Two BQO: of well Founded LT
-- statement:
--   **Well-orders are 2-BQO.** If `f` is bad for a well-order `<`, the sequence `n ↦ f (n, n+1)`
--   is strictly decreasing, contradicting well-foundedness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L152-L160
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean#L152-L160

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

theorem TwoBQO.of_wellFoundedLT {α : Type*} [LinearOrder α] [WellFoundedLT α] :
    TwoBQO (α := α) (· ≤ ·) := by sorry
