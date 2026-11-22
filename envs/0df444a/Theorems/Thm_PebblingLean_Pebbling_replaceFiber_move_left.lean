-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_replaceFiber_move_left
-- name    : PebblingLean.Pebbling.replaceFiber_move_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:41.922121+00:00
-- url     : https://prove2.me/theorems/c3010f03-01a6-43a2-b997-ceb1e35f969f
-- title:
--   Pebbling: replace Fiber move left
-- statement:
--   One move in the first factor can be replayed inside a fixed fiber of the
--   Cartesian product, leaving all other fibers unchanged.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L108-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L108-L136

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

theorem PebblingLean.Pebbling.replaceFiber_move_left [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E F : Pebbling V} {Fs : W → Pebbling V} {z : W}
    (hmove : Move G E F) :
    Move (Graph.cartesianProduct G H)
      (fibersDistribution (replaceFiber Fs z E))
      (fibersDistribution (replaceFiber Fs z F)) := by sorry
