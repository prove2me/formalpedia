-- Prove2me | Theorems.Thm_WeldedPath_crossing_probability_bound
-- name    : WeldedPath.crossing_probability_bound
-- status  : Open
-- author  : @dmilosch
-- created : 2026-11-17T16:16:31.932535+00:00
-- url     : https://prove2.me/theorems/7ec53d6c-39c6-4742-9520-2d007d76e29f
-- title:
--   Small-query crossing probability for the exact compressed welded-tree oracle
-- statement:
--   Put $N=2^n$, $N_l=2^{n-l}$, and $\epsilon_l=2^{-l}$. There are absolute constants $C_0,C>0$ such that, for every even $n\ge16$, every $2\le l\le n-4$, every valid properly colored welded-tree instance, and every $q\ge1$ query algorithm with any finite workspace, the conditions
--   $$
--   C_0(q+1)\le N_l,\qquad
--   C_0\left((q+1)\epsilon_l+\frac{(n+1)(q+1)^3}{N}\right)\le\frac12
--   $$
--   imply
--   $$
--   p_{\rm cross}(A)\le C\left(q^2\epsilon_l+\frac{nq^3}{N}\right).
--   $$
--   The probability is that Algorithm 3.10 records a crossing after running $A$ against the exact compressed oracle from the empty database. This isolates the accumulated good-space error and crossing exclusion in the proof of Theorem 4.1. Both constants are chosen before all graph and algorithm parameters.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/pdf/2611.05912v1. Eq. (49), p.27; Eq. (53), p.28; Proposition 4.12, pp.41-42; Section 4.5, p.44, Eq. (75) and the following crossing-probability inequality. The corresponding equations are (56) and (78) in https://arxiv.org/html/2611.05912v1. The bound is the squared accumulated good-space error, with Eq. (49) retained.

import Mathlib
import Definitions.Def_WeldedPath_Supplement_pCross

namespace WeldedPath

open QAlgorithms Supplement

theorem crossing_probability_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q,
      C₀ * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      C₀ * (((q : ℝ) + 1) / (2 : ℝ) ^ l +
        ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤ 1 / 2 →
      pCross l G A ≤ C * ((q : ℝ) ^ 2 / (2 : ℝ) ^ l +
        (n : ℝ) * (q : ℝ) ^ 3 / (2 : ℝ) ^ n) := by sorry

end WeldedPath
