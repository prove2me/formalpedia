-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_size_fibersDistribution
-- name    : PebblingLean.Pebbling.size_fibersDistribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:40.657771+00:00
-- url     : https://prove2.me/theorems/ed815e26-2e8c-466c-8982-13f718b74257
-- title:
--   Pebbling: size fibers Distribution
-- statement:
--   Total size of a fiber-assembled product distribution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L74-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L74-L80

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

theorem PebblingLean.Pebbling.size_fibersDistribution [Fintype V] [Fintype W] (F : W → Pebbling V) :
    size (fibersDistribution F) = ∑ z, size (F z) := by sorry
