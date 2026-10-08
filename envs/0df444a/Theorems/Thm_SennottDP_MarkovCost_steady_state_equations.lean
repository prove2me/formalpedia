-- Prove2me | Theorems.Thm_SennottDP_MarkovCost_steady_state_equations
-- name    : SennottDP.MarkovCost.steady_state_equations
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T13:46:19.015533+00:00
-- url     : https://prove2.me/theorems/daf5f28e-7b63-4863-8461-bc41e8c4be74
-- title:
--   Proposition C.1.2 — steady state equations on a positive recurrent class, and $\pi_j = e_{ij}/m_{ii}$
-- statement:
--   Let $\Gamma$ be a Markov chain on a countable state space $S$ with transition probabilities $P_{ij}$, and let $R$ be a positive recurrent class with steady state probabilities $\pi_j = (m_{jj})^{-1}$.
--
--   1. The steady state probabilities solve
--   $$ \pi_j = \sum_{i \in R} P_{ij}\pi_i \quad (j \in R), \qquad \sum_{j \in R} \pi_j = 1, $$
--   and every nonnegative solution $(x_j)$ of these equations satisfies $x_j = \pi_j$ for $j \in R$.
--   2. For $i, j \in R$ let $e_{ij}$ be the expected number of visits to $j$ during a first passage from $i$ to $i$ (visits at times $0 \le t < T_{ii}$). Then
--   $$ \pi_j = \frac{e_{ij}}{m_{ii}} = \pi_i e_{ij}. $$
--
--   The first part identifies the steady state probabilities as the unique stationary distribution of the class; the second expresses them through a single excursion from a reference state.
--
--   **Formalization Note** $e_{ij}$ is `visits M {i} i j`; values are in $[0,\infty]$ and the candidate solutions $x$ are `ℝ≥0∞`-valued (the normalization forces them finite on $R$).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 295, Proposition C.1.2

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Proposition C.1.2, p. 295. Let `R` be a positive recurrent class.
(i) `π_j = ∑_{i ∈ R} P_{ij} π_i` for `j ∈ R` and `∑_{j ∈ R} π_j = 1`, and every nonnegative solution
of these equations equals `π` on `R`.
(ii) For `i, j ∈ R`, with `e_{ij} = _{\{i\}} u_{ij}` the expected number of visits to `j` during a
first passage from `i` to `i`, `π_j = e_{ij} / m_{ii} = π_i e_{ij}`. -/
theorem steady_state_equations {S : Type} [Countable S] (M : MC S) (R : Set S)
    (hR : IsPosRecClass M R) :
    ((∀ j ∈ R, steadyState M j = ∑' i : R, M.P i j * steadyState M i) ∧
      ∑' j : R, steadyState M j = 1 ∧
      ∀ x : S → ℝ≥0∞, (∀ j ∈ R, x j = ∑' i : R, M.P i j * x i) → ∑' j : R, x j = 1 →
        ∀ j ∈ R, x j = steadyState M j) ∧
    (∀ i ∈ R, ∀ j ∈ R,
      steadyState M j = visits M {i} i j / meanPassage M {i} i ∧
      steadyState M j = steadyState M i * visits M {i} i j) := by sorry

end SennottDP.MarkovCost
