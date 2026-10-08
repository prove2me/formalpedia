-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_lemma_4_6
-- name    : PoissonDepTrials.MixInv.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:05:43.457787+00:00
-- url     : https://prove2.me/theorems/5e55ea89-6400-4f94-a9c8-6d7da519bb47
-- title:
--   Lemma 4.6, p. 540 — |Σ E[(X_i − p_i)f(V^{(i)} + 1)]| ≤ 6‖f‖nφ(m + 1)
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, with $p_i=P(X_i=1)=1-P(X_i=0)$, padded by $X_i\equiv 0$ for $i\le 0$ and $i\ge n+1$. Write $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. Assume Ibragimov's mixing condition (4.1): there is a non-increasing sequence $\varphi(k)\downarrow 0$ such that for all $j,k\ge 1$ and every event $B\in\mathcal M_{j+k,\infty}$, $|P(B\mid\mathcal M_{1j})-P(B)|\le\varphi(k)$ almost surely, where $\mathcal M_{a,b}=\sigma(X_i: a\le i\le b)$. Let $m\ge0$ and let $f$ be a bounded function on the nonnegative integers with $|f|\le M$. Then
--   $$\Bigl|\sum_{i=1}^nE\bigl[(X_i-p_i)f(V^{(i)}+1)\bigr]\Bigr|\le6Mn\varphi(m+1).$$
--   It bounds the middle error term of (2.6).
--
--   **Formalization Note** The trials are $X:\mathbb N\to\Omega\to\mathbb N$ with `IsBernoulliTrials` (measurable, zero outside $[1,n]$, at most $1$ almost surely); $p_i$ is the definition `prob`, so it cannot disagree with $X$. Constant padding variables generate the trivial $\sigma$-algebra, so (4.1) for the padded sequence is (4.1) for $X_1,\dots,X_n$. Double sums over $|i-j|$ are computed in $\mathbb Z$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 540, Lemma 4.6, (4.11)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem lemma_4_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ)
    (f : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) :
    |∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P|
      ≤ 6 * M * n * φ (m + 1) := by sorry

end PoissonDepTrials.MixInv
