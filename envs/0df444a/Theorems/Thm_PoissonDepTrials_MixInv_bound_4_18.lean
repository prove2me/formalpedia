-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_bound_4_18
-- name    : PoissonDepTrials.MixInv.bound_4_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:08:38.235083+00:00
-- url     : https://prove2.me/theorems/5dec7e0a-cd36-4ac1-b9b7-a767a5610b49
-- title:
--   (4.18), proof of Theorem 4.2, p. 542 — E{X_iX_j[1 + 2 min(λ^{−1/2},1)|Y′_{i,j−1} + 1 − λ|]} ≤ [EX_iX_j][8m + 5 + 4(nφ(m+1))^{1/2}] + 8 min(λ^{−1/2},1)(np_i + λ)φ(m+1)
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, with $p_i=P(X_i=1)=1-P(X_i=0)$, padded by $X_i\equiv 0$ for $i\le 0$ and $i\ge n+1$. Write $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. Assume Ibragimov's mixing condition (4.1): there is a non-increasing sequence $\varphi(k)\downarrow 0$ such that for all $j,k\ge 1$ and every event $B\in\mathcal M_{j+k,\infty}$, $|P(B\mid\mathcal M_{1j})-P(B)|\le\varphi(k)$ almost surely, where $\mathcal M_{a,b}=\sigma(X_i: a\le i\le b)$. For $m\ge0$ and indices $i,j\in[1,n]$ with $0<|i-j|\le m$,
--   $$E\Bigl\{X_iX_j\bigl[1+2\min(\lambda^{-1/2},1)|Y'_{i,j-1}+1-\lambda|\bigr]\Bigr\}\le\bigl[EX_iX_j\bigr]\bigl[8m+5+4(n\varphi(m+1))^{1/2}\bigr]+8\min(\lambda^{-1/2},1)(np_i+\lambda)\varphi(m+1).$$
--   It bounds each summand of the first double sum of (4.14).
--
--   **Formalization Note** The trials are $X:\mathbb N\to\Omega\to\mathbb N$ with `IsBernoulliTrials` (measurable, zero outside $[1,n]$, at most $1$ almost surely); $p_i$ is the definition `prob`, so it cannot disagree with $X$. Constant padding variables generate the trivial $\sigma$-algebra, so (4.1) for the padded sequence is (4.1) for $X_1,\dots,X_n$. Double sums over $|i-j|$ are computed in $\mathbb Z$. $\min(\lambda^{-1/2},1)$ is `min (1 / Real.sqrt λ) 1` and $(n\varphi(m+1))^{1/2}$ is `Real.sqrt (n * φ (m + 1))`.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 542, proof of Theorem 4.2, (4.18)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem bound_4_18 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) (i j : ℕ)
    (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n)
    (hij : 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m) :
    ∫ ω, (X i ω : ℝ) * X j ω *
        (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y' n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P
      ≤ (∫ ω, (X i ω : ℝ) * X j ω ∂P) * (8 * m + 5 + 4 * Real.sqrt ((n : ℝ) * φ (m + 1)))
        + 8 * min (1 / Real.sqrt (lam P n X)) 1 * (n * prob P X i + lam P n X) * φ (m + 1) := by sorry

end PoissonDepTrials.MixInv
