-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
-- name    : PebblingLean.Pebbling.sliceDistribution_apply_on
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:31.080855+00:00
-- url     : https://prove2.me/theorems/bcbb78d7-5bce-44b9-bb45-ae2ec6dfff84
-- title:
--   Pebbling: slice Distribution apply on
-- statement:
--   The Pebbling construction uses the slice Distribution apply on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L96-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L96-L98

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

theorem PebblingLean.Pebbling.sliceDistribution_apply_on [DecidableEq V] (x : V) (E : Pebbling W) (z : W) :
    sliceDistribution x E (x, z) = E z := by sorry
