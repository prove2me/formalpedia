-- Prove2me | Theorems.Thm_SimplexProj_Condat_condat_algorithm_correct
-- name    : SimplexProj.Condat.condat_algorithm_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T23:53:29.671615+00:00
-- url     : https://prove2.me/theorems/ff4d2611-4b3e-4fbc-9dc1-1c58f8c9709e
-- title:
--   Correctness of Condat's Proposed Algorithm (Fig. 2): the output is $P_\Delta(y)$ and $K$ counts its nonzeros
-- statement:
--   Let $N \ge 1$, $y = (y_1, \dots, y_N) \in \mathbb{R}^N$ and $a > 0$. Run Condat's Proposed Algorithm (Fig. 2) on $y$ and $a$; it terminates with a threshold $\tau$ and a count $K$. Set $x_n := \max\{y_n - \tau, 0\}$ for $n = 1, \dots, N$ (step 6). Then $x$ is the Euclidean projection of $y$ onto the simplex of radius $a$, and $K$ is the number of nonzero entries of $x$:
--
--   $$x = P_\Delta(y), \qquad K = \#\{\, n \in \{1, \dots, N\} : x_n \ne 0 \,\}.$$
--
--   This is the correctness claim of Condat's algorithm (Fig. 2 and its caption, argued in Sect. 3): the algorithm computes the projection exactly and in finite time, for every input, with no assumption on the order or distinctness of the entries of $y$.
--
--   **Formalization Note.** The algorithm is the total function `condatAlgorithm a (List.ofFn y)`, returning $(\tau, K)$; termination is part of the definition (well-founded recursion), so the theorem is about every input. $x = P_\Delta(y)$ is the predicate `IsSimplexProjection a y x`; $K$ is compared with the number of indices $n$ with $x_n \ne 0$ (a count over indices, not distinct values).
-- source:
--   Condat, Fast Projection onto the Simplex and the ℓ1 Ball, HAL hal-01056171v2, p. 6, Sect. 3, Fig. 2 and caption

import Mathlib
import Definitions.Def_SimplexProj_Condat_IsSimplexProjection
import Definitions.Def_SimplexProj_Condat_condatAlgorithm

namespace SimplexProj.Condat

/-- Condat, Sect. 3, Fig. 2 and its caption (p. 6): for `N ≥ 1`, `y ∈ ℝ^N`, `a > 0`, the
Proposed Algorithm run on `(y_1, …, y_N)` terminates with `(τ, K)` such that
`x = (max {y_n - τ, 0})_{n=1}^N` (step 6) is the Euclidean projection `P_Δ(y)` of `y` onto the
simplex of radius `a`, and `K` is the number of nonzero elements of `x`. -/
theorem condat_algorithm_correct (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 0 < a) (y : Fin N → ℝ)
    (τ : ℝ) (K : ℕ) (hout : condatAlgorithm a (List.ofFn y) = (τ, K)) :
    IsSimplexProjection a y (fun n => max (y n - τ) 0) ∧
      K = (Finset.univ.filter (fun n => max (y n - τ) 0 ≠ 0)).card := by sorry

end SimplexProj.Condat
