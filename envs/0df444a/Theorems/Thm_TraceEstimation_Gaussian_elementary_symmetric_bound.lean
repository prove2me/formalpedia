-- Prove2me | Theorems.Thm_TraceEstimation_Gaussian_elementary_symmetric_bound
-- name    : TraceEstimation.Gaussian.elementary_symmetric_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:28:43.358509+00:00
-- url     : https://prove2.me/theorems/9017ce75-3779-4bad-a829-05e87af54bed
-- title:
--   Section 5, p. 8:8 — elementary symmetric sums and the bound on $|h(t)|$
-- statement:
--   Two elementary estimates used in the proof of Theorem 5.2.
--
--   1. Let $x_1, \ldots, x_n$ be non-negative real numbers. For every $i = 1, \ldots, n$,
--   $$\sum_{\substack{S \subseteq [n] \\ |S| = i}} \prod_{j\in S} x_j \le \left(\sum_{j=1}^{n} x_j\right)^i .$$
--   2. Let $\lambda_1, \ldots, \lambda_n \ge 0$, let $\tau = \sum_j \lambda_j$ and let $h$ be the higher-order term $h(t) = \sum_{s=2}^{n}(-2)^s t^s \sum_{|S| = s} \prod_{i\in S} \lambda_i$. For every $t \ge 0$,
--   $$|h(t)| \le \sum_{j=2}^{n}(2\tau t)^j .$$
--
--   In the paper the $\lambda_i$ are the eigenvalues of a symmetric positive semi-definite matrix $A$, so they are non-negative and $\tau = \mathrm{trace}(A)$; the bound controls the correction term in the moment generating function (1).
--
--   **Formalization Note** Part 2 is stated for an arbitrary non-negative vector $\lambda$, which includes the eigenvalue vector of any positive semi-definite matrix. The page states part 2 without the range of $t$; the proof uses it at $t = t_0 > 0$, and $t \ge 0$ is the range in which it follows from part 1.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:8, Section 5, first and second unnumbered displays

import Mathlib
import Definitions.Def_TraceEstimation_Gaussian_hPoly

namespace TraceEstimation.Gaussian

/-- Section 5, p. 8:8, first two displays (Avron–Toledo). (a) For non-negative reals
`x_1, …, x_n` and every `i = 1, …, n`, `∑_{S ⊆ [n], |S| = i} ∏_{j ∈ S} x_j ≤ (∑_j x_j)^i`.
(b) Consequently, for non-negative eigenvalues `λ_1, …, λ_n` with `τ = ∑ λ_j` and every
`t ≥ 0`, `|h(t)| ≤ ∑_{j=2}^n (2 τ t)^j`. -/
theorem elementary_symmetric_bound {n : ℕ} :
    (∀ x : Fin n → ℝ, (∀ j, 0 ≤ x j) → ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard i, ∏ j ∈ S, x j ≤ (∑ j, x j) ^ i) ∧
    (∀ lam : Fin n → ℝ, (∀ j, 0 ≤ lam j) → ∀ t : ℝ, 0 ≤ t →
      |hPoly lam t| ≤ ∑ j ∈ Finset.Icc 2 n, (2 * (∑ k, lam k) * t) ^ j) := by sorry

end TraceEstimation.Gaussian
