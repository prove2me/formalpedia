-- Prove2me | Theorems.Thm_PrivSeqLearn_QueryComplexity_theorem_4_1
-- name    : PrivSeqLearn.QueryComplexity.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:22.533787+00:00
-- url     : https://prove2.me/theorems/0eb872f8-0aa7-4aac-aeca-83ba64292884
-- title:
--   Theorem 4.1, p. 12 — max{log 1/ϵ, log δ/ϵ + 2L − 4} ≤ N*(ϵ,δ,L) ≤ log 1/(Lϵ) + 2L for 2ϵ < δ ≤ 1/L
-- statement:
--   **Theorem 4.1 (Query Complexity of Private Sequential Learning).** Fix $\epsilon > 0$, $\delta > 0$ and a positive integer $L \ge 2$ such that $2\epsilon < \delta \le 1/L$. Then
--   $$\max\left\{ \left\lceil \log_2 \frac1\epsilon \right\rceil,\ \left\lceil \log_2 \frac\delta\epsilon \right\rceil + 2L - 4 \right\} \le N^*(\epsilon,\delta,L) \le \left\lceil \log_2 \frac{1}{L\epsilon} \right\rceil + 2L.$$
--
--   Here $N^*(\epsilon, \delta, L)$ is the least number of queries of a learner strategy (with values in $[0,1)$ and distinct queries) that locates the true value to within $\epsilon/2$ for every true value and seed, while keeping the adversary's information set uncoverable by fewer than $L$ intervals of length $\delta$. Without privacy, bisection needs $\lceil \log_2(1/\epsilon) \rceil$ queries, so the price of privacy is at most an additive $2L$.
--
--   **Formalization Note** All logarithms are base 2 and every non-integer term is rounded up (footnote 1, p. 4); the bounds are computed in $\mathbb Z$. In the regime, all three logarithm arguments exceed $1$. $N^*$ is the minimum over $\mathbb N$ of eq. (5), p. 11; the upper bound shows the set is nonempty.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 12, Theorem 4.1 (eq. (7)), with footnote 1, p. 4

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting

namespace PrivSeqLearn.QueryComplexity

/-- Theorem 4.1 (Query Complexity of Private Sequential Learning) (Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 12): fix `ϵ > 0`,
`δ > 0` and a positive integer `L ≥ 2` such that `2ϵ < δ ≤ 1/L`. Then
`max {log 1/ϵ, log δ/ϵ + 2L − 4} ≤ N*(ϵ, δ, L) ≤ log 1/(Lϵ) + 2L` (7).

**Formalization Note** Logarithms are base 2 and every non-integer is rounded up (footnote 1, p. 4):
each log term is `⌈log₂ ·⌉`, computed in `ℤ`. `N*` is the `sInf` over `ℕ` of the lengths `N` for which
`Φ_N` (values in `[0, 1)`, distinct queries) contains an `(ϵ, δ, L)`-private strategy, eq. (5), p. 11. -/
theorem theorem_4_1 (ϵ δ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hδ : 0 < δ) (hL : 2 ≤ L)
    (h2ϵδ : 2 * ϵ < δ) (hδL : δ ≤ 1 / (L : ℝ)) :
    max ⌈Real.logb 2 (1 / ϵ)⌉ (⌈Real.logb 2 (δ / ϵ)⌉ + 2 * (L : ℤ) - 4) ≤ (Nstar ϵ δ L : ℤ) ∧
      (Nstar ϵ δ L : ℤ) ≤ ⌈Real.logb 2 (1 / ((L : ℝ) * ϵ))⌉ + 2 * (L : ℤ) := by sorry

end PrivSeqLearn.QueryComplexity
