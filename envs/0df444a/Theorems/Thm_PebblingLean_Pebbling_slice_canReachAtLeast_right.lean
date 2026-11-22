-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_slice_canReachAtLeast_right
-- name    : PebblingLean.Pebbling.slice_canReachAtLeast_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:48.664266+00:00
-- url     : https://prove2.me/theorems/5b966bd3-70ff-454b-9673-ca967dbbc830
-- title:
--   Pebbling: slice can Reach At Least right
-- statement:
--   If `E` solves a target in the second factor, then the corresponding slice
--   distribution solves the corresponding product target.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L254-L260
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L254-L260

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

theorem PebblingLean.Pebbling.slice_canReachAtLeast_right [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E : Pebbling W} {x : V} {target : W} {T : ℕ}
    (hcan : CanReachAtLeast H E target T) :
    CanReachAtLeast (Graph.cartesianProduct G H) (sliceDistribution x E) (x, target) T := by sorry
