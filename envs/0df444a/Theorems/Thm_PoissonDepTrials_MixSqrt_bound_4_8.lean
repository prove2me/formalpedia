-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_bound_4_8
-- name    : PoissonDepTrials.MixSqrt.bound_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:25.950865+00:00
-- url     : https://prove2.me/theorems/2c862c9f-3bbb-41f4-b622-7cb9b9a089df
-- title:
--   (4.8), p. 540 — |Σ_i E[(X_i − p_i)V^{(i)}]| ≤ 4λnφ(m + 1)
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, possibly dependent, with $p_i=P(X_i=1)$, and put $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. As on p. 535, $X_i$ is taken to be identically zero when $i\le 0$ or $i\ge n+1$. Assume that $X_1,\dots,X_n$ satisfy Ibragimov's mixing condition (4.1) with a nonincreasing sequence $\varphi(k)\downarrow 0$. Fix $m\ge0$. Then
--   $$\Bigl|\sum_{i=1}^nE\bigl[(X_i-p_i)V^{(i)}\bigr]\Bigr|\le4\lambda n\varphi(m+1).$$
--
--   This bounds the last term of the variance identity (4.7); with (4.7) and (4.10) it gives Lemma 4.5.
--
--   **Formalization Note** The trials are a sequence $X:\mathbb N\to\Omega\to\mathbb N$ that is measurable, almost surely $\{0,1\}$-valued, and identically $0$ at index $0$ and above $n$ (the paper's padding convention, which changes no $\sigma$-algebra). $p_i$ is defined as $P(X_i=1)$, not a free parameter. The statement is the first and last members of the chain (4.8) on p. 540.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 540, proof of Lemma 4.4, (4.8)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), proof of Lemma 4.4, p. 540, (4.8): for Bernoulli trials satisfying (4.1),
`|Σ_{i=1}^n E[(X_i − p_i)V^{(i)}]| ≤ 4λnφ(m + 1)`. -/
theorem bound_4_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) :
    |∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) ∂P|
      ≤ 4 * lam P n X * n * φ (m + 1) := by sorry

end PoissonDepTrials.MixSqrt
