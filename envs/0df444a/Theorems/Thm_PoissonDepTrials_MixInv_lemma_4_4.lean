-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_lemma_4_4
-- name    : PoissonDepTrials.MixInv.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:07:29.781987+00:00
-- url     : https://prove2.me/theorems/bc4bee1a-5739-4f81-b9e8-3b5594f20ce1
-- title:
--   Lemma 4.4, p. 540 — [Var W]^{1/2} ≤ λ^{1/2}[m + 1 + 2(nφ(m + 1))^{1/2}]
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, with $p_i=P(X_i=1)=1-P(X_i=0)$, padded by $X_i\equiv 0$ for $i\le 0$ and $i\ge n+1$. Write $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. Assume Ibragimov's mixing condition (4.1): there is a non-increasing sequence $\varphi(k)\downarrow 0$ such that for all $j,k\ge 1$ and every event $B\in\mathcal M_{j+k,\infty}$, $|P(B\mid\mathcal M_{1j})-P(B)|\le\varphi(k)$ almost surely, where $\mathcal M_{a,b}=\sigma(X_i: a\le i\le b)$. Then for every $m\ge0$,
--   $$[\operatorname{Var}(W)]^{1/2}\le\lambda^{1/2}\bigl[m+1+2(n\varphi(m+1))^{1/2}\bigr].$$
--   In the proof of Theorem 4.2 it is applied to subsums of the trials to control $E|V^{(i,j)}-EV^{(i,j)}|$.
--
--   **Formalization Note** The trials are $X:\mathbb N\to\Omega\to\mathbb N$ with `IsBernoulliTrials` (measurable, zero outside $[1,n]$, at most $1$ almost surely); $p_i$ is the definition `prob`, so it cannot disagree with $X$. Constant padding variables generate the trivial $\sigma$-algebra, so (4.1) for the padded sequence is (4.1) for $X_1,\dots,X_n$. Double sums over $|i-j|$ are computed in $\mathbb Z$. $\min(\lambda^{-1/2},1)$ is `min (1 / Real.sqrt λ) 1` and $(n\varphi(m+1))^{1/2}$ is `Real.sqrt (n * φ (m + 1))`.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 540, Lemma 4.4, (4.6)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem lemma_4_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) :
    Real.sqrt (Var[fun ω => (W n X ω : ℝ); P]) ≤
      Real.sqrt (lam P n X) * (m + 1 + 2 * Real.sqrt ((n : ℝ) * φ (m + 1))) := by sorry

end PoissonDepTrials.MixInv
