-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_uniform_fiber_bound_minPile
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_uniform_fiber_bound_minPile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:54:06.964672+00:00
-- url     : https://prove2.me/theorems/88961472-a75b-4836-b212-4be4a1165dc4
-- title:
--   Hypercube: has Solvable At Most Size split product of uniform fiber bound min Pile
-- statement:
--   Uniform fiber recurrence with occupied-pile compression.  If each occupied
--   pile of `E` has at least `S` pebbles, and a `Tfiber`-solvable construction in
--   `Q_a` costs at most `S*K`, then the product cost is bounded by `|E|*K`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L266-L281
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubeProduct.lean#L266-L281

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

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_uniform_fiber_bound_minPile
    {a m Tbase Tfiber S K : ℕ} {E : Pebbling (HypercubeVertex m)}
    (hTbase : 1 ≤ Tbase)
    (hE : Pebbling.SolvableAtLeast (graph m) E Tbase)
    (hpile_le : ∀ z : HypercubeVertex m, E z ≤ Tfiber)
    (hmin : Pebbling.MinOccupiedPileSize E S)
    (hfiber : Pebbling.HasSolvableAtMostSize (graph a) Tfiber (S * K)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (Pebbling.size E * K) := by sorry
