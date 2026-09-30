-- Prove2me | Theorems.Thm_SupplyChainTheory_reduced_matrix_bound
-- name    : SupplyChainTheory.reduced_matrix_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:52:40.58341+00:00
-- url     : https://prove2.me/theorems/081f996d-b302-4d85-b48e-d9903ca0a5d6
-- title:
--   Theorem 10.1 (Little et al.): after reducing rows by $\rho_i \ge 0$ and columns by $\kappa_j \ge 0$ with all reduced entries nonnegative, $\sum_i \rho_i + \sum_j \kappa_j \le z^*$
-- statement:
--   **Theorem 10.1.** Let $c'_{ij} = c_{ij} - \rho_i - \kappa_j$ for all $i \ne j$, where
--   $\rho_i, \kappa_j \ge 0$ are constants such that $c'_{ij} \ge 0$ for all $i \ne j$. Then
--   $h = \sum_i \rho_i + \sum_j \kappa_j$ is a lower bound on the optimal tour length $z^*$.
--
--   Every tour, traversed in one direction, leaves each node once and enters each node once, so its
--   length under $c'$ is its length under $c$ minus exactly $h$; being nonnegative under $c'$, it is
--   at least $h$ under $c$. This is the bounding device of Little et al.'s branch-and-bound.
--
--   **Formalization Note** The book applies the reduction to the upper-triangular matrix only
--   ($i < j$) and asserts the same conclusion. That version is false: node $n$ is never a row and
--   node $1$ never a column of a triangular entry, so $\rho_n$ (or $\kappa_1$) may be arbitrarily
--   large, and even with the row and column reductions restricted to the entries that exist, a
--   random metric instance violates the bound (see the mission's checks). The statement here is the
--   full-matrix reduction, which is what Little et al. prove and what makes the bookkeeping exact.
--   It needs at least two nodes. With $n = 1$ the only "tour" is the self-loop $c_{11}$, no entry
--   $i \ne j$ constrains $\rho_1$ or $\kappa_1$, and the bound fails for large $\rho_1$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 408-409, Sect. 10.3.2, Theorem 10.1 and the preceding derivation; after Little, Murty, Sweeney and Karel (1963)

import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem reduced_matrix_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hn : 2 ≤ n) (ρ κ : Fin n → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ i j, i ≠ j → 0 ≤ reducedCost c ρ κ i j) :
    ∑ i, ρ i + ∑ j, κ j ≤ optTourLength c := by sorry

end SupplyChainTheory
