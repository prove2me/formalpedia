-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_demand_cost
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_demand_cost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:54:05.882597+00:00
-- url     : https://prove2.me/theorems/ec914ce2-551f-4245-bb58-d1f1b715facb
-- title:
--   Hypercube: has Solvable At Most Size split product of demand cost
-- statement:
--   Product step where the first-factor cost depends only on the demand value
--   `E z`, not on the fiber location `z`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L187-L199
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L187-L199

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

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_demand_cost
    {a m : ℕ} {E : Pebbling (HypercubeVertex m)} {demandCost : ℕ → ℕ}
    (hE : Pebbling.Solvable (graph m) E)
    (hcost :
      ∀ T : ℕ, T ≠ 0 →
        Pebbling.HasSolvableAtMostSize (graph a) T (demandCost T)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else demandCost (E z)) := by sorry
