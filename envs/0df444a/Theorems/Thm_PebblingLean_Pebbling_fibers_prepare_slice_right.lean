-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_fibers_prepare_slice_right
-- name    : PebblingLean.Pebbling.fibers_prepare_slice_right
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:48:50.934811+00:00
-- url     : https://prove2.me/theorems/2f56b817-defe-4e4f-8c64-25cdf34241b9
-- title:
--   Pebbling: fibers prepare slice right
-- statement:
--   If every fiber can prepare the number of pebbles prescribed by `E` at the
--   same first-coordinate target `x`, then the product distribution can be moved to
--   a distribution dominating the slice `{x} × W` with profile `E`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L291-L306
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L291-L306

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

theorem PebblingLean.Pebbling.fibers_prepare_slice_right [Finite W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E : Pebbling W} {F : W → Pebbling V} {x : V}
    (hcan : ∀ z : W, CanReachAtLeast G (F z) x (E z)) :
    ∃ Dprep : Pebbling (V × W),
      Reaches (Graph.cartesianProduct G H) (fibersDistribution F) Dprep ∧
        Dominates Dprep (sliceDistribution x E) := by sorry
