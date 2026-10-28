-- Prove2me | Theorems.Thm_WeightedAverage_gauss_real
-- name    : WeightedAverage.gauss_real
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T16:24:26.998837+00:00
-- url     : https://prove2.me/theorems/2b130f69-feab-492a-b929-5f64b6319f27
-- title:
--   $\sum_{i<n}(i+1) = n(n+1)/2$ over the reals
-- statement:
--   For every $n \in \mathbb{N}$,
--
--   $$
--   \sum_{i=0}^{n-1} (i+1) \;=\; \frac{n(n+1)}{2},
--   $$
--
--   as an identity between real numbers.
--
--   Mathlib proves the Gauss sum over $\mathbb{N}$, `Finset.sum_range_id_mul_two` and
--   `Gauss_sum`-style results, but a convergence-rate proof needs it on the right-hand side of a
--   division, with the summand already cast to $\mathbb{R}$ so that `field_simp` and `linarith`
--   can use it. This is that form: the weights $i+1$ that define a weighted ergodic average
--   $\bar x^k = \frac{2}{(k+1)(k+2)}\sum_{i=0}^{k}(i+1)x^i$ sum to $(k+1)(k+2)/2$, which is where
--   the normalization comes from.
--
--   **Formalization Note** The summand is `((i : ℝ) + 1)`, i.e. the cast of `i` plus the real `1`,
--   not the cast of `i + 1`; the two agree by `push_cast` but only one of them appears in a goal
--   produced by `Finset.sum_range_succ`.
-- source:
--   The normalizing constant of the weighted ergodic average in Davis & Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017) 829-858, DOI 10.1007/s11228-017-0421-z, proof of Theorem 3.2, p. 840.

import Mathlib

namespace WeightedAverage

/-- $\sum_{i<n}(i+1) = n(n+1)/2$, over the reals. -/
theorem gauss_real (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by sorry

end WeightedAverage
