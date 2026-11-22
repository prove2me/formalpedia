-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_highDemand_demand_cost
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_highDemand_demand_cost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:54:16.015561+00:00
-- url     : https://prove2.me/theorems/9afefec6-b641-4857-b2c2-8be0ed868247
-- title:
--   Hypercube: has Solvable At Most Size split product of high Demand demand cost
-- statement:
--   If the second factor is `T`-solvable with `T ≥ 1`, it may be used as the
--   solvable demand pattern in the product step.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L228-L239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L228-L239

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

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_highDemand_demand_cost
    {a m T : ℕ} {E : Pebbling (HypercubeVertex m)} {demandCost : ℕ → ℕ}
    (hT : 1 ≤ T)
    (hE : Pebbling.SolvableAtLeast (graph m) E T)
    (hcost :
      ∀ t : ℕ, t ≠ 0 →
        Pebbling.HasSolvableAtMostSize (graph a) t (demandCost t)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else demandCost (E z)) := by sorry
