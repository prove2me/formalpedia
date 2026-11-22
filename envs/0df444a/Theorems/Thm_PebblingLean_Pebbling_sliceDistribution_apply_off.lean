-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
-- name    : PebblingLean.Pebbling.sliceDistribution_apply_off
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:30.303711+00:00
-- url     : https://prove2.me/theorems/1417560d-5d6e-4536-a109-494439d42225
-- title:
--   Pebbling: slice Distribution apply off
-- statement:
--   The Pebbling construction uses the slice Distribution apply off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L101-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L101-L104

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}

theorem PebblingLean.Pebbling.sliceDistribution_apply_off [DecidableEq V] {x x' : V} (E : Pebbling W) (z : W)
    (h : x' ≠ x) :
    sliceDistribution x E (x', z) = 0 := by sorry
