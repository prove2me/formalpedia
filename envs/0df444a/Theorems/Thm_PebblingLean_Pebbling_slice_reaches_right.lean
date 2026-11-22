-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_slice_reaches_right
-- name    : PebblingLean.Pebbling.slice_reaches_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:45.182624+00:00
-- url     : https://prove2.me/theorems/69980f0d-faf8-41ab-a429-95dd9bba616d
-- title:
--   Pebbling: slice reaches right
-- statement:
--   A pebbling sequence in the second factor can be replayed inside a fixed
--   slice of the product.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L242-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L242-L250

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

theorem PebblingLean.Pebbling.slice_reaches_right [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E F : Pebbling W} {x : V}
    (hreach : Reaches H E F) :
    Reaches (Graph.cartesianProduct G H) (sliceDistribution x E) (sliceDistribution x F) := by sorry
