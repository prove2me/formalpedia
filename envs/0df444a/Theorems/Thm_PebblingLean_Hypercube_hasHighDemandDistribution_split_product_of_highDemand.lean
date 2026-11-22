-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_split_product_of_highDemand
-- name    : PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_highDemand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:54:07.528731+00:00
-- url     : https://prove2.me/theorems/40959d81-83c2-4c55-833f-a24a121d3d09
-- title:
--   Hypercube: has High Demand Distribution split product of high Demand
-- statement:
--   High-demand product recurrence preserving the next pile-size invariant.
--   The same high-demand fiber construction in `Q_a` is reused for every occupied
--   fiber over `Q_m`; occupied-pile compression in the `Q_m` distribution pays for
--   this reuse.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L309-L378
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L309-L378

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

theorem PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_highDemand
    {a m Tbase costBound S K Snew : ℕ}
    (hTbase : 1 ≤ Tbase)
    (hhigh : HasHighDemandDistribution m Tbase costBound S)
    (hfiber : HasHighDemandDistribution a costBound (S * K) Snew) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) Snew := by sorry
