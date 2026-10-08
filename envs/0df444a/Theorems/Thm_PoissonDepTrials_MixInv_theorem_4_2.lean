-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_theorem_4_2
-- name    : PoissonDepTrials.MixInv.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:24:07.080985+00:00
-- url     : https://prove2.me/theorems/5f2cbe01-7f3c-4e1e-b042-7c20d3df76a4
-- title:
--   Theorem 4.2, p. 541 — |Eh(W) − 𝒫_λh| ≤ 2λ^{−1}[8m+5+4(nφ(m+1))^{1/2}][Var W − λ + 2(2m+1)Σp_i²] + 32[6m+3+(nφ(m+1))^{1/2}]nφ(m+1)
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, with $p_i=P(X_i=1)=1-P(X_i=0)$, padded by $X_i\equiv 0$ for $i\le 0$ and $i\ge n+1$. Write $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. Assume Ibragimov's mixing condition (4.1): there is a non-increasing sequence $\varphi(k)\downarrow 0$ such that for all $j,k\ge 1$ and every event $B\in\mathcal M_{j+k,\infty}$, $|P(B\mid\mathcal M_{1j})-P(B)|\le\varphi(k)$ almost surely, where $\mathcal M_{a,b}=\sigma(X_i: a\le i\le b)$. Then for every $m=0,1,2,\dots$ and every real function $h$ on the nonnegative integers with $|h|\le1$,
--   $$\begin{aligned}|Eh(W)-\mathcal P_\lambda h|\le{}&2\lambda^{-1}\bigl[8m+5+4(n\varphi(m+1))^{1/2}\bigr]\Bigl[\operatorname{Var}(W)-\lambda+2(2m+1)\sum_{i=1}^np_i^2\Bigr]\\&+32\bigl[6m+3+(n\varphi(m+1))^{1/2}\bigr]n\varphi(m+1),\end{aligned}$$
--   where $\mathcal P_\lambda h=e^{-\lambda}\sum_{k\ge0}h(k)\lambda^k/k!$ is the expectation of $h$ under the Poisson law with mean $\lambda$.
--
--   Since $\sup_{|h|\le1}|Eh(W)-\mathcal P_\lambda h|$ is twice the total variation distance between the law of $W$ and the Poisson law, this is an explicit Poisson approximation for sums of dependent trials. Its first term has order $\lambda^{-1}$, which improves on Theorem 4.1's $\min(\lambda^{-1/2},1)$ when $\lambda$ is large.
--
--   **Formalization Note** The trials are $X:\mathbb N\to\Omega\to\mathbb N$ with `IsBernoulliTrials` (measurable, zero outside $[1,n]$, at most $1$ almost surely); $p_i$ is the definition `prob`, so it cannot disagree with $X$. Constant padding variables generate the trivial $\sigma$-algebra, so (4.1) for the padded sequence is (4.1) for $X_1,\dots,X_n$. Double sums over $|i-j|$ are computed in $\mathbb Z$. $\min(\lambda^{-1/2},1)$ is `min (1 / Real.sqrt λ) 1` and $(n\varphi(m+1))^{1/2}$ is `Real.sqrt (n * φ (m + 1))`. No hypothesis $\lambda>0$ is added: at $\lambda=0$ every $p_i=0$, $W=0$ almost surely, and both sides are $0$ with Lean's $0^{-1}=0$, as in the paper. The factor $\lambda^{-1}$ is the bare $\lambda^{-1}$ of the paper, not $\min(\lambda^{-1},1)$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 541, Theorem 4.2, (4.13); proof pp. 541–542, (4.14)–(4.19)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem theorem_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ)
    (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h| ≤
      2 * (lam P n X)⁻¹ * (8 * m + 5 + 4 * Real.sqrt ((n : ℝ) * φ (m + 1)))
          * (Var[fun ω => (W n X ω : ℝ); P] - lam P n X
              + 2 * (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2)
        + 32 * (6 * m + 3 + Real.sqrt ((n : ℝ) * φ (m + 1))) * n * φ (m + 1) := by sorry

end PoissonDepTrials.MixInv
