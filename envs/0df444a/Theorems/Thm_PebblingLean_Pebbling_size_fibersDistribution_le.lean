-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_size_fibersDistribution_le
-- name    : PebblingLean.Pebbling.size_fibersDistribution_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:33.895791+00:00
-- url     : https://prove2.me/theorems/f9448aaf-9f09-47b0-92de-8ff08b9865a0
-- title:
--   Pebbling: size fibers Distribution le
-- statement:
--   A pointwise fiber cost bound gives a product cost bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L83-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L83-L88

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

theorem PebblingLean.Pebbling.size_fibersDistribution_le [Fintype V] [Fintype W] {F : W → Pebbling V}
    {cost : W → ℕ} (hcost : ∀ z : W, size (F z) ≤ cost z) :
    size (fibersDistribution F) ≤ ∑ z, cost z := by sorry
