-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_lemma_4_6
-- name    : PoissonDepTrials.MixSqrt.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:16.087695+00:00
-- url     : https://prove2.me/theorems/31884a72-761a-4e6f-bd42-e790dfe6bcc3
-- title:
--   Lemma 4.6, p. 540 — |Σ_i E[(X_i − p_i)f(V^{(i)} + 1)]| ≤ 6‖f‖nφ(m + 1)
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, possibly dependent, with $p_i=P(X_i=1)$, and put $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. As on p. 535, $X_i$ is taken to be identically zero when $i\le 0$ or $i\ge n+1$. Assume that $X_1,\dots,X_n$ satisfy Ibragimov's mixing condition (4.1) with a nonincreasing sequence $\varphi(k)\downarrow 0$. Fix $m\ge0$. Then for every function $f$ on the nonnegative integers with $|f|\le M$,
--   $$\Bigl|\sum_{i=1}^nE\bigl[(X_i-p_i)f(V^{(i)}+1)\bigr]\Bigr|\le6M\,n\,\varphi(m+1).$$
--
--   Applied with $f=S_\lambda h$ and Lemma 3.3, this bounds the middle error term of (2.6) by $24\min(\lambda^{-1/2},1)\,n\varphi(m+1)$.
--
--   **Formalization Note** The trials are a sequence $X:\mathbb N\to\Omega\to\mathbb N$ that is measurable, almost surely $\{0,1\}$-valued, and identically $0$ at index $0$ and above $n$ (the paper's padding convention, which changes no $\sigma$-algebra). $p_i$ is defined as $P(X_i=1)$, not a free parameter. $\|f\|$ is an arbitrary bound $M$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 540, Lemma 4.6, (4.11)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Lemma 4.6, p. 540, (4.11). For Bernoulli trials satisfying (4.1) and every
function `f` on the nonnegative integers bounded by `M`,
`|Σ_{i=1}^n E[(X_i − p_i)f(V^{(i)} + 1)]| ≤ 6‖f‖nφ(m + 1)`. -/
theorem lemma_4_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) :
    |∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P|
      ≤ 6 * M * n * φ (m + 1) := by sorry

end PoissonDepTrials.MixSqrt
