-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_split_product_of_highDemand_variable
-- name    : PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_highDemand_variable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:54:14.591808+00:00
-- url     : https://prove2.me/theorems/90316c12-0d76-4d8a-b17e-52aaf3550e9e
-- title:
--   Hypercube: has High Demand Distribution split product of high Demand variable
-- statement:
--   Variable-demand high-demand product recurrence.
--
--   This is the paper-facing product step.  If an occupied second-factor pile has
--   size `s_z`, we use a first-factor construction for demand `s_z` and cost
--   `s_z*K`.  Summing over occupied fibers gives total cost `|E|*K`, and the
--   high-demand bound on `E` then gives `costBound*K`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L386-L457
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L386-L457

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

theorem PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_highDemand_variable
    {a m Tbase costBound S K Snew : ℕ}
    (hTbase : 1 ≤ Tbase)
    (hhigh : HasHighDemandDistribution m Tbase costBound S)
    (hfiber :
      ∀ t : ℕ, S ≤ t → HasHighDemandDistribution a t (t * K) Snew) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) Snew := by sorry
