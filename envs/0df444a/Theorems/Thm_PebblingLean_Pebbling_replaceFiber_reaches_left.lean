-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_replaceFiber_reaches_left
-- name    : PebblingLean.Pebbling.replaceFiber_reaches_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:46.049154+00:00
-- url     : https://prove2.me/theorems/f6c7ec50-ed33-4045-88d7-c3dcadd9469d
-- title:
--   Pebbling: replace Fiber reaches left
-- statement:
--   A pebbling sequence in the first factor can be replayed inside a fixed
--   fiber of the product.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L140-L151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L140-L151

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

theorem PebblingLean.Pebbling.replaceFiber_reaches_left [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E F : Pebbling V} {Fs : W → Pebbling V} {z : W}
    (hreach : Reaches G E F) :
    Reaches (Graph.cartesianProduct G H)
      (fibersDistribution (replaceFiber Fs z E))
      (fibersDistribution (replaceFiber Fs z F)) := by sorry
