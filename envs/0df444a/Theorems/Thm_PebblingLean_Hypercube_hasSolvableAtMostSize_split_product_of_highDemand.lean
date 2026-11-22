-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_highDemand
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_highDemand
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:54:09.052377+00:00
-- url     : https://prove2.me/theorems/011d9962-ca1a-428b-ae9d-0f0931e7aab3
-- title:
--   Hypercube: has Solvable At Most Size split product of high Demand
-- statement:
--   Recurrence step from a high-demand distribution.  If `Q_m` has a
--   `Tbase`-solvable distribution of size at most `costBound` whose occupied piles
--   have size at least `S`, and `Q_a` can solve demand `costBound` with cost
--   `S*K`, then `Q_(a+m)` has a solvable distribution with cost `costBound*K`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L287-L303
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L287-L303

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

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_highDemand
    {a m Tbase costBound S K : ℕ}
    (hTbase : 1 ≤ Tbase)
    (hhigh : HasHighDemandDistribution m Tbase costBound S)
    (hfiber : Pebbling.HasSolvableAtMostSize (graph a) costBound (S * K)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1 (costBound * K) := by sorry
