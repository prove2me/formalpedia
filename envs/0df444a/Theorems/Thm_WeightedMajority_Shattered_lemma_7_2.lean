-- Prove2me | Theorems.Thm_WeightedMajority_Shattered_lemma_7_2
-- name    : WeightedMajority.Shattered.lemma_7_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:06.78611+00:00
-- url     : https://prove2.me/theorems/d5ed7c76-76a1-4e82-86ad-cf9003cccb5d
-- title:
--   Lemma 7.2 — subset of powers of two with prescribed sum
-- statement:
--   Let $r_1,\ldots,r_j$ be positive powers of two with integer exponents, and let $\ell\in\mathbb Z$. If every $r_i\le2^\ell$ and $2^\ell\le\sum_{i=1}^j r_i$, then a subset $K$ has exactly the target weight:
--
--   $$
--   \sum_{i\in K}r_i=2^\ell.
--   $$
--
--   The lemma extracts a prescribed weight from a collection of dyadic weights.
--
--   **Formalization Note** Each hypothesis $\log_2 r_i\in\mathbb Z$ is represented as $r_i=2^{k_i}$ for an integer $k_i$. The upper bound on each weight expresses the source's maximum condition without taking a maximum of an empty family; when $j=0$, the total-weight condition is impossible.
-- source:
--   Littlestone and Warmuth, The Weighted Majority Algorithm, Information and Computation 108 (1994), p. 244, Lemma 7.2; https://doi.org/10.1006/inco.1994.1009

import Mathlib

namespace WeightedMajority.Shattered

/-- Littlestone--Warmuth, Lemma 7.2, p. 244. `r i = 2 ^ k i` encodes
the assertion that `log₂ (r i)` is an integer. -/
theorem lemma_7_2 {j : ℕ} (r : Fin j → ℝ) (k : Fin j → ℤ)
    (hr : ∀ i, r i = (2 : ℝ) ^ (k i)) (l : ℤ)
    (hmax : ∀ i, r i ≤ (2 : ℝ) ^ l)
    (hsum : (2 : ℝ) ^ l ≤ ∑ i, r i) :
    ∃ K : Finset (Fin j), ∑ i ∈ K, r i = (2 : ℝ) ^ l := by sorry

end WeightedMajority.Shattered
