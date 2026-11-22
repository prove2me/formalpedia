-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_hasSolvableAtMostSize_product_of_fiber_demands
-- name    : PebblingLean.Pebbling.hasSolvableAtMostSize_product_of_fiber_demands
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:48:58.706437+00:00
-- url     : https://prove2.me/theorems/97dad339-b93f-435b-ad00-c9054a231407
-- title:
--   Pebbling: has Solvable At Most Size product of fiber demands
-- statement:
--   Costed form of the deterministic product step, matching the recursive
--   upper-bound bookkeeping: only occupied vertices of `E` need nonzero demand
--   distributions in the first factor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L329-L352
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L329-L352

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

theorem PebblingLean.Pebbling.hasSolvableAtMostSize_product_of_fiber_demands
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E : Pebbling W} {cost : W → ℕ}
    (hE : Solvable H E)
    (hcost : ∀ z : W, E z ≠ 0 → HasSolvableAtMostSize G (E z) (cost z)) :
    HasSolvableAtMostSize (Graph.cartesianProduct G H) 1
      (∑ z, if E z = 0 then 0 else cost z) := by sorry
