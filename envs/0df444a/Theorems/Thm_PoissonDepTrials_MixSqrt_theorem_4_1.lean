-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_theorem_4_1
-- name    : PoissonDepTrials.MixSqrt.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:35.277975+00:00
-- url     : https://prove2.me/theorems/50ef7d44-7eee-4cae-bf9f-7834575382c7
-- title:
--   Theorem 4.1, p. 541 — |Eh(W) − 𝒫_λh| ≤ 6 min(λ^{−1/2}, 1)[Var(W) − λ + 2(2m+1)Σp_i² + 4(λ+1)nφ(m+1)] under (4.1)
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, possibly dependent, with $p_i=P(X_i=1)$, and put $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. As on p. 535, $X_i$ is taken to be identically zero when $i\le 0$ or $i\ge n+1$. Assume that $X_1,\dots,X_n$ satisfy Ibragimov's mixing condition (4.1) with a nonincreasing sequence $\varphi(k)\downarrow 0$. Let $\mathcal P_\lambda h=e^{-\lambda}\sum_{k\ge0}h(k)\lambda^k/k!$ be the expectation of $h$ under the Poisson distribution with mean $\lambda$.
--
--   Then for every $m=0,1,2,\dots$ and every real function $h$ on the nonnegative integers with $|h|\le1$,
--   $$\bigl|Eh(W)-\mathcal P_\lambda h\bigr|\le6\min(\lambda^{-1/2},1)\Bigl[\operatorname{Var}(W)-\lambda+2(2m+1)\sum_{i=1}^np_i^2+4(\lambda+1)n\varphi(m+1)\Bigr].$$
--
--   Taking the supremum over $h$ bounds the total variation distance between the law of $W$ and the Poisson law with the same mean. The bound is explicit, holds for every $m$, and for $m$-dependent trials ($\varphi(m+1)=0$) and independent trials ($m=0$) it specializes to Theorem 4.3 and Le Cam's bound (Corollary 4.1).
--
--   **Formalization Note** The trials are a sequence $X:\mathbb N\to\Omega\to\mathbb N$ that is measurable, almost surely $\{0,1\}$-valued, and identically $0$ at index $0$ and above $n$ (the paper's padding convention, which changes no $\sigma$-algebra). $p_i$ is defined as $P(X_i=1)$, not a free parameter. Condition (4.1) is `IbragimovMixing`. $\lambda^{-1/2}$ is written $1/\sqrt\lambda$; no hypothesis $\lambda>0$ is added: when $\lambda=0$ every trial vanishes almost surely, both sides are $0$, and Lean's $1/\sqrt0=0$ keeps the statement true.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 541, Theorem 4.1, (4.12)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Theorem 4.1, p. 541, (4.12). Let `X_1, …, X_n` be Bernoulli trials satisfying
Ibragimov's mixing condition (4.1), `W = Σ X_i`, `λ = Σ p_i`. For every `m = 0, 1, 2, …` and every
`h` on the nonnegative integers with `|h| ≤ 1`,
`|Eh(W) − 𝒫_λh| ≤ 6 min(λ^{−1/2}, 1)[Var(W) − λ + 2(2m + 1)Σ p_i² + 4(λ + 1)nφ(m + 1)]`. -/
theorem theorem_4_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h|
      ≤ 6 * min (1 / Real.sqrt (lam P n X)) 1 * (Var[fun ω => (W n X ω : ℝ); P] - lam P n X
        + 2 * (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 + 4 * (lam P n X + 1) * n * φ (m + 1)) := by sorry

end PoissonDepTrials.MixSqrt
