-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_bound_4_14
-- name    : PoissonDepTrials.MixInv.bound_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:08:13.871913+00:00
-- url     : https://prove2.me/theorems/919bdaf6-e0ed-4219-9fce-5910d1a7719a
-- title:
--   (4.14), proof of Theorem 4.2, p. 541 — |Eh(W) − 𝒫_λh| bounded by the Y′- and Y-weighted double sums plus 24 min(λ^{−1/2}, 1)nφ(m + 1)
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, with $p_i=P(X_i=1)=1-P(X_i=0)$, padded by $X_i\equiv 0$ for $i\le 0$ and $i\ge n+1$. Write $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. Assume Ibragimov's mixing condition (4.1): there is a non-increasing sequence $\varphi(k)\downarrow 0$ such that for all $j,k\ge 1$ and every event $B\in\mathcal M_{j+k,\infty}$, $|P(B\mid\mathcal M_{1j})-P(B)|\le\varphi(k)$ almost surely, where $\mathcal M_{a,b}=\sigma(X_i: a\le i\le b)$. Assume $\lambda>0$, fix $m\ge0$ and $h$ with $|h|\le1$. Then
--   $$\begin{aligned}|Eh(W)-\mathcal P_\lambda h|\le{}&2\lambda^{-1}\sum\sum_{0<|i-j|\le m}E\Bigl\{X_iX_j\bigl[1+2\min(\lambda^{-1/2},1)\,|Y'_{i,j-1}+1-\lambda|\bigr]\Bigr\}\\&+2\lambda^{-1}\sum\sum_{|i-j|\le m}p_iE\Bigl\{X_j\bigl[1+2\min(\lambda^{-1/2},1)\,|Y_{i,j-1}+1-\lambda|\bigr]\Bigr\}\\&+24\min(\lambda^{-1/2},1)\,n\varphi(m+1).\end{aligned}$$
--   Note that the first double sum uses $Y'$ and the second $Y$. This is the first step of the proof of Theorem 4.2: (2.6) bounded through Lemmas 3.3, 3.5 and 4.6.
--
--   **Formalization Note** The trials are $X:\mathbb N\to\Omega\to\mathbb N$ with `IsBernoulliTrials` (measurable, zero outside $[1,n]$, at most $1$ almost surely); $p_i$ is the definition `prob`, so it cannot disagree with $X$. Constant padding variables generate the trivial $\sigma$-algebra, so (4.1) for the padded sequence is (4.1) for $X_1,\dots,X_n$. Double sums over $|i-j|$ are computed in $\mathbb Z$. $\min(\lambda^{-1/2},1)$ is `min (1 / Real.sqrt λ) 1` and $(n\varphi(m+1))^{1/2}$ is `Real.sqrt (n * φ (m + 1))`. $\lambda>0$ is stated because the display is derived from (2.6), where $S_\lambda h$ needs $\lambda>0$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 541, proof of Theorem 4.2, (4.14)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem bound_4_14 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hlam : 0 < lam P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ)
    (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h| ≤
      2 * (lam P n X)⁻¹ * (∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            ∫ ω, (X i ω : ℝ) * X j ω *
              (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y' n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P)
      + 2 * (lam P n X)⁻¹ * (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            prob P X i * ∫ ω, (X j ω : ℝ) *
              (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P)
      + 24 * min (1 / Real.sqrt (lam P n X)) 1 * n * φ (m + 1) := by sorry

end PoissonDepTrials.MixInv
