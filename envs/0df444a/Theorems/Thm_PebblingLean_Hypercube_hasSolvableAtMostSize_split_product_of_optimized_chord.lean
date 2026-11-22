-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_optimized_chord
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_optimized_chord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:05:49.953032+00:00
-- url     : https://prove2.me/theorems/ee0be25a-c9a0-4e9d-a435-1628afcbe623
-- title:
--   Hypercube: has Solvable At Most Size split product of optimized chord
-- statement:
--   One formal recursion step from the optimized chord high-demand construction.
--
--   The probabilistic construction supplies a `Tbase`-solvable distribution on
--   `Q_m` of size at most `N * 2^rOut`, with occupied piles of size at least
--   `2^rOut`.  If `Q_a` can solve demand `N * 2^rOut` at cost `2^rOut * K`, then
--   the product step gives a solvable distribution on `Q_(a+m)` of cost
--   `(N * 2^rOut) * K`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L95-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean#L95-L121

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_optimized_chord
    {a m N rIn rOut Tbase K : ℕ} {gap : ℝ}
    (hTbase : 1 ≤ Tbase)
    (hgap_pos : 0 < gap)
    (hmean :
      (Tbase : ℝ) + gap ≤
        (N : ℝ) * (annulusMean m rIn rOut : ℝ))
    (hlog :
      ((m + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean m rIn rOut : ℝ))))
    (hfiber :
      Pebbling.HasSolvableAtMostSize (graph a)
        (N * 2 ^ rOut) (2 ^ rOut * K)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      ((N * 2 ^ rOut) * K) := by sorry
