-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_of_dominates_slice_right
-- name    : PebblingLean.Pebbling.canReachAtLeast_of_dominates_slice_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:47.504801+00:00
-- url     : https://prove2.me/theorems/9fc9d71f-95fe-4363-8974-b3883f39c1e0
-- title:
--   Pebbling: can Reach At Least of dominates slice right
-- statement:
--   Once a product distribution dominates a prepared slice, any target reachable
--   from the slice is also reachable from the product distribution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L264-L271
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L264-L271

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

theorem PebblingLean.Pebbling.canReachAtLeast_of_dominates_slice_right [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {D : Pebbling (V × W)} {E : Pebbling W}
    {x : V} {target : W} {T : ℕ}
    (hdom : Dominates D (sliceDistribution x E))
    (hcan : CanReachAtLeast H E target T) :
    CanReachAtLeast (Graph.cartesianProduct G H) D (x, target) T := by sorry
