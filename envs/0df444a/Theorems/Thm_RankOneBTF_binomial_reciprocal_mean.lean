-- Prove2me | Theorems.Thm_RankOneBTF_binomial_reciprocal_mean
-- name    : RankOneBTF.binomial_reciprocal_mean
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:22:40.892346+00:00
-- url     : https://prove2.me/theorems/ac9226f4-cebd-4912-93f5-e7584ca14e27
-- title:
--   $\mathbb E[1/(1+X)]=\frac{1-(1-\bar p)^{N+1}}{(N+1)\bar p}$ for $X\sim\mathrm{Bin}(N,\bar p)$
-- statement:
--   Let $X$ be a binomial random variable with parameters $(N,\bar p)$, $0<\bar p\le1$. Then
--   $$
--   \mathbb E\Bigl[\frac1{1+X}\Bigr]=\sum_{k=0}^{N}\binom Nk\bar p^{\,k}(1-\bar p)^{N-k}\frac1{1+k}=\frac{1}{(N+1)\bar p}\bigl(1-(1-\bar p)^{N+1}\bigr).
--   $$
--
--   The identity evaluates the expected reciprocal of the uncorrupted counts in the proofs of Claims 3 and 7 (with $\bar p=1-p$).
--
--   **Formalization Note** The expectation is written as the explicit binomial sum.
--
--   Differences from the source:
--   - encoding: a binomial parameter p̄ (the paper applies it with p̄ = 1 − p ∈ (0,1]) → 0 < p̄ ≤ 1; reason: at p̄ = 0 the right-hand side is undefined; this excludes only that case
--   - encoding: E[1/(1+X)] for X ~ Bin(N, p̄) → the explicit sum Σ_k C(N,k) p̄^k (1−p̄)^{N−k}/(1+k); reason: the definition of the expectation
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, p.22, proof of Claim 3: "for a binomial random variable X with parameters (N, p̄), we have E[1/(1+X)] = (1/((N+1)p̄))(1 − (1 − p̄)^{N+1})"; also Step 1 of Claim 7, p.36

import Mathlib

namespace RankOneBTF

/-- **Binomial reciprocal identity** (arXiv:2202.07053v3, p.22, proof of Claim 3: "for a
binomial random variable X with parameters (N, p̄), we have
E[1/(1+X)] = (1/((N+1)p̄))(1 − (1 − p̄)^{N+1})"; also used in Steps 1 and 2 of Claim 7, p.36).

**Formalization Note** `E[1/(1+X)]` for `X ~ Bin(N, p̄)` is written as the explicit sum
`Σ_{k=0}^{N} C(N,k) p̄^k (1−p̄)^{N−k} / (1+k)`. The success probability satisfies
`0 < p̄ ≤ 1`: at `p̄ = 0` the right-hand side is undefined. -/
theorem binomial_reciprocal_mean (N : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∑ k ∈ Finset.range (N + 1),
        (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k) / (1 + (k : ℝ)) =
      1 / (((N : ℝ) + 1) * q) * (1 - (1 - q) ^ (N + 1)) := by sorry

end RankOneBTF
