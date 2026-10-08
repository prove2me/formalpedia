-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_lemma_4_5
-- name    : PoissonDepTrials.MixSqrt.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:27.973982+00:00
-- url     : https://prove2.me/theorems/d6b7da4b-35e5-4a43-bbdb-21692d2d20fe
-- title:
--   Lemma 4.5, p. 540 — ΣΣ_{0<|i−j|≤m} EX_iX_j ≤ Var(W) − λ + (2m + 1)Σp_i² + 4λnφ(m + 1)
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, possibly dependent, with $p_i=P(X_i=1)$, and put $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. As on p. 535, $X_i$ is taken to be identically zero when $i\le 0$ or $i\ge n+1$. Assume that $X_1,\dots,X_n$ satisfy Ibragimov's mixing condition (4.1) with a nonincreasing sequence $\varphi(k)\downarrow 0$. Fix $m\ge0$. Then
--   $$\sum\sum_{0<|i-j|\le m}EX_iX_j\le\operatorname{Var}(W)-\lambda+(2m+1)\sum_{i=1}^np_i^2+4\lambda n\varphi(m+1).$$
--
--   This turns the first error term of (2.6) into a quantity expressed by $\operatorname{Var}(W)$, $\lambda$ and the $p_i$; with (4.10) it closes the proof of Theorem 4.1.
--
--   **Formalization Note** The trials are a sequence $X:\mathbb N\to\Omega\to\mathbb N$ that is measurable, almost surely $\{0,1\}$-valued, and identically $0$ at index $0$ and above $n$ (the paper's padding convention, which changes no $\sigma$-algebra). $p_i$ is defined as $P(X_i=1)$, not a free parameter.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 540, Lemma 4.5, (4.9)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Lemma 4.5, p. 540, (4.9): for Bernoulli trials satisfying (4.1),
`ΣΣ_{0<|i−j|≤m} EX_iX_j ≤ Var(W) − λ + (2m + 1) Σ_i p_i² + 4λnφ(m + 1)`. -/
theorem lemma_4_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
        ∫ ω, (X i ω : ℝ) * X j ω ∂P
      ≤ Var[fun ω => (W n X ω : ℝ); P] - lam P n X + (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2
        + 4 * lam P n X * n * φ (m + 1) := by sorry

end PoissonDepTrials.MixSqrt
