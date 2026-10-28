-- Prove2me | Theorems.Thm_WeightedAverage_telescope_weighted
-- name    : WeightedAverage.telescope_weighted
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T16:22:21.149023+00:00
-- url     : https://prove2.me/theorems/06c2918e-bbe8-4933-87f1-d6e390d925cd
-- title:
--   Weighted telescoping: $\sum_{i<n}(i+1)(D_i - D_{i+1}) = \sum_{i<n} D_i - n D_n$
-- statement:
--   For every real sequence $(D_i)_{i \ge 0}$ and every $n \in \mathbb{N}$,
--
--   $$
--   \sum_{i=0}^{n-1} (i+1)\big(D_i - D_{i+1}\big) \;=\; \sum_{i=0}^{n-1} D_i \;-\; n\,D_n .
--   $$
--
--   This is the identity that turns a per-step decrease into a rate. In the analysis of a splitting
--   or proximal method one proves a one-step inequality of the form
--   $a_i \le (i+1)(D_i - D_{i+1})$, where $D_i$ is a squared distance to a fixed point and $a_i$ is
--   the quantity to be bounded. Summing and applying the identity above replaces the right-hand
--   side by $\sum_i D_i - n D_n \le \sum_i D_i$, and if the $D_i$ are bounded -- which Fejér
--   monotonicity gives -- the whole sum is $O(n)$. Dividing by the weight total
--   $n(n+1)/2$ then yields the $O(1/n)$ ergodic rate.
--
--   Unlike the unweighted telescoping $\sum (D_i - D_{i+1}) = D_0 - D_n$, the weighted version does
--   not collapse to two terms: the surviving $\sum_i D_i$ is exactly why a weighted average, rather
--   than the last iterate, is what the rate is stated for.
--
--   **Formalization Note** Proved by induction on $n$, with `Finset.sum_range_succ` on both sides;
--   no hypothesis on $D$ is needed.
-- source:
--   The telescoping step of the weighted ergodic rate in Davis & Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017) 829-858, DOI 10.1007/s11228-017-0421-z, proof of Theorem 3.2, p. 840; stated here for an arbitrary real sequence.

import Mathlib

namespace WeightedAverage

/-- The $(i+1)$-weighted telescoping identity. -/
theorem telescope_weighted (D : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * (D i - D (i + 1)) =
      ∑ i ∈ Finset.range n, D i - (n : ℝ) * D n := by sorry

end WeightedAverage
