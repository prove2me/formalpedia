-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_single_apply_ne
-- name    : PebblingLean.Pebbling.single_apply_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:50.375334+00:00
-- url     : https://prove2.me/theorems/774ce3bc-c129-40a5-949d-4b87fff73970
-- title:
--   Pebbling: single apply ne
-- statement:
--   The Pebbling construction uses the single apply ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L92-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L92-L94

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

theorem PebblingLean.Pebbling.single_apply_ne [DecidableEq V] {u v : V} (k : ℕ) (h : u ≠ v) :
    single v k u = 0 := by sorry
