-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_single_eq_twoPoint_left_zero
-- name    : PebblingLean.Pebbling.single_eq_twoPoint_left_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:31.562804+00:00
-- url     : https://prove2.me/theorems/02721f77-28bc-40ab-92ba-e4f3963e66fe
-- title:
--   Pebbling: single eq two Point left zero
-- statement:
--   The Pebbling construction uses the single eq two Point left zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L136-L146
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L136-L146

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_PebblingLean_Delivery
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}

theorem PebblingLean.Pebbling.single_eq_twoPoint_left_zero [DecidableEq V] {u v : V} (k : ℕ) (huv : u ≠ v) :
    single v k = twoPoint u v 0 k := by sorry
