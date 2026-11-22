-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_fibers_reaches_of_forall_reaches
-- name    : PebblingLean.Pebbling.fibers_reaches_of_forall_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:46.132551+00:00
-- url     : https://prove2.me/theorems/26b3d541-10db-443a-b900-5d60c4abbec1
-- title:
--   Pebbling: fibers reaches of forall reaches
-- statement:
--   Independent first-factor preparations in every fiber can be composed into
--   one product pebbling sequence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L155-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L155-L214

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

theorem PebblingLean.Pebbling.fibers_reaches_of_forall_reaches [Finite W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {F F' : W → Pebbling V}
    (hreach : ∀ z : W, Reaches G (F z) (F' z)) :
    Reaches (Graph.cartesianProduct G H) (fibersDistribution F) (fibersDistribution F') := by sorry
