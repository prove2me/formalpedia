-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_fiber_demands
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_fiber_demands
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:54:03.906845+00:00
-- url     : https://prove2.me/theorems/10bd0696-0845-4386-b7cb-0f40fb9bccc2
-- title:
--   Hypercube: has Solvable At Most Size split product of fiber demands
-- statement:
--   Hypercube-specific deterministic product step.  A solvable distribution
--   `E` on `Q_m` specifies how many pebbles must be prepared in each `Q_a` fiber;
--   if those fiber demands can be met within the given costs, then `Q_(a+m)` has a
--   solvable distribution with the summed cost.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L167-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L167-L183

module
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finite.Prod
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_fiber_demands
    {a m : ℕ} {E : Pebbling (HypercubeVertex m)}
    {cost : HypercubeVertex m → ℕ}
    (hE : Pebbling.Solvable (graph m) E)
    (hcost :
      ∀ z : HypercubeVertex m,
        E z ≠ 0 → Pebbling.HasSolvableAtMostSize (graph a) (E z) (cost z)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else cost z) := by sorry
