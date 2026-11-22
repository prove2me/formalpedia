-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_uniform_fiber_bound
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_uniform_fiber_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:53:59.075818+00:00
-- url     : https://prove2.me/theorems/05d88a42-d1d1-44a6-8666-bf7965a666cf
-- title:
--   Hypercube: has Solvable At Most Size split product of uniform fiber bound
-- statement:
--   Uniform high-demand fiber recurrence.  If `E` is a `T`-solvable
--   second-factor distribution and every occupied pile of `E` has size at most
--   `Tfiber`, then one `Tfiber`-solvable construction in `Q_a` can be reused for
--   every occupied fiber.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L245-L261
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L245-L261

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

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_uniform_fiber_bound
    {a m Tbase Tfiber K : ℕ} {E : Pebbling (HypercubeVertex m)}
    (hTbase : 1 ≤ Tbase)
    (hE : Pebbling.SolvableAtLeast (graph m) E Tbase)
    (hpile_le : ∀ z : HypercubeVertex m, E z ≤ Tfiber)
    (hfiber : Pebbling.HasSolvableAtMostSize (graph a) Tfiber K) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (Pebbling.supportSize E * K) := by sorry
