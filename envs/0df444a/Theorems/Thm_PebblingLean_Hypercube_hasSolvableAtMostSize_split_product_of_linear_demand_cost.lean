-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_linear_demand_cost
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_linear_demand_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:54:16.388973+00:00
-- url     : https://prove2.me/theorems/90ef4a19-e449-42fb-a1be-71e29fbf2ee3
-- title:
--   Hypercube: has Solvable At Most Size split product of linear demand cost
-- statement:
--   Linear fiber-demand recurrence: if every demand `T` in `Q_a` can be solved
--   with at most `K*T` pebbles, then using a solvable distribution `E` on `Q_m` as
--   the second-factor demand pattern costs at most `K * |E|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L204-L224
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L204-L224

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

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_linear_demand_cost
    {a m K : ℕ} {E : Pebbling (HypercubeVertex m)}
    (hE : Pebbling.Solvable (graph m) E)
    (hcost :
      ∀ T : ℕ,
        Pebbling.HasSolvableAtMostSize (graph a) T (K * T)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (K * Pebbling.size E) := by sorry
