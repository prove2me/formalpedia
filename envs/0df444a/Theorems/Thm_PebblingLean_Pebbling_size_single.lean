-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_size_single
-- name    : PebblingLean.Pebbling.size_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:50.746907+00:00
-- url     : https://prove2.me/theorems/5a281f43-c4aa-4670-95a5-80d533fcf347
-- title:
--   Pebbling: size single
-- statement:
--   The Pebbling construction uses the size single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L97-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L97-L100

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

theorem PebblingLean.Pebbling.size_single [Fintype V] [DecidableEq V] (v : V) (k : ℕ) :
    size (single v k) = k := by sorry
