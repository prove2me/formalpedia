-- Prove2me | Theorems.Thm_RobustSAA_Univariate_watson_bound
-- name    : RobustSAA.Univariate.watson_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:14.002017+00:00
-- url     : https://prove2.me/theorems/7c4894e4-2688-4500-a786-105410107fb3
-- title:
--   §10.7, p. 39 — W_N² − U_N² = ((1/N)ΣF₀(ξ^(i)) − 1/2)² ≤ max{…} in terms of D′_N(F₀)
-- statement:
--   Let $N\ge1$, let $\xi^1,\dots,\xi^N\in\mathbb R$ have order statistics $\xi^{(1)}\le\dots\le\xi^{(N)}$, let $F_0$ be a probability distribution on $\mathbb R$, and let $D'_N(F_0)=\max_i|F_0(\xi^{(i)})-\tfrac{2i-1}{2N}|$. With $W_N$ the Cramér–von Mises and $U_N$ the Watson statistic (8),
--
--   $$
--   \begin{aligned}
--   W_N^2-U_N^2&=\Big(\frac1N\sum_{i=1}^NF_0(\xi^{(i)})-\frac12\Big)^2\\
--   &\le\max\Big\{\Big(\frac1N\sum_{i=1}^N\min\Big\{1,\frac{2i-1}{2N}+D'_N(F_0)\Big\}-\frac12\Big)^2,\ \Big(\frac1N\sum_{i=1}^N\max\Big\{0,\frac{2i-1}{2N}-D'_N(F_0)\Big\}-\frac12\Big)^2\Big\}.
--   \end{aligned}
--   $$
--
--   This controls the centring term by which the Watson statistic differs from the CvM statistic.
--
--   **Formalization Note** Lean indices are 0-based (Lean's `i` is the paper's $i+1$), and the order statistics are the sorted sample `s ∘ Tuple.sort s`. The statement assumes $N\ge1$, which the paper's statistics presuppose.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §10.7, proof of Theorem 5, p. 39, display before "Letting M"

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

namespace RobustSAA.Univariate

open Filter MeasureTheory

/-- §10.7, p. 39: `W_N² − U_N² = ((1/N) Σ F₀(ξ^(i)) − 1/2)²`, which is at most the larger of the
two squared extremes obtained from `|F₀(ξ^(i)) − (2i−1)/(2N)| ≤ D′_N(F₀)` and `0 ≤ F₀ ≤ 1`. -/
theorem watson_bound {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) :
    cvmStat F₀ s ^ 2 - watsonStat F₀ s ^ 2 = meanDev F₀ s ^ 2 ∧
    meanDev F₀ s ^ 2 ≤
      max ((1 / (N : ℝ) * ∑ i : Fin N,
              min 1 ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N) + Dprime F₀ s) - 1 / 2) ^ 2)
          ((1 / (N : ℝ) * ∑ i : Fin N,
              max 0 ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N) - Dprime F₀ s) - 1 / 2) ^ 2) := by sorry

end RobustSAA.Univariate
