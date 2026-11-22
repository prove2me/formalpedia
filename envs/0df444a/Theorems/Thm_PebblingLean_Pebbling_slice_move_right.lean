-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_slice_move_right
-- name    : PebblingLean.Pebbling.slice_move_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:47.165445+00:00
-- url     : https://prove2.me/theorems/7f3416e5-65fe-41ff-9b15-93d759563657
-- title:
--   Pebbling: slice move right
-- statement:
--   One move in the second factor can be replayed inside a fixed product slice.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L217-L238
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L217-L238

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

theorem PebblingLean.Pebbling.slice_move_right [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E F : Pebbling W} {x : V}
    (hmove : Move H E F) :
    Move (Graph.cartesianProduct G H) (sliceDistribution x E) (sliceDistribution x F) := by sorry
