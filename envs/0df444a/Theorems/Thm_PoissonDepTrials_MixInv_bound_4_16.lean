-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_bound_4_16
-- name    : PoissonDepTrials.MixInv.bound_4_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:08:23.746455+00:00
-- url     : https://prove2.me/theorems/d6f38dc4-b3db-4164-9ad3-ec7a6c70ce9d
-- title:
--   (4.16), proof of Theorem 4.2, p. 541 — E|V^{(i,j)} − EV^{(i,j)}| ≤ [Var V^{(i,j)}]^{1/2} ≤ λ^{1/2}[m + 1 + 2(nφ(m + 1))^{1/2}]
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, with $p_i=P(X_i=1)=1-P(X_i=0)$, padded by $X_i\equiv 0$ for $i\le 0$ and $i\ge n+1$. Write $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. Assume Ibragimov's mixing condition (4.1): there is a non-increasing sequence $\varphi(k)\downarrow 0$ such that for all $j,k\ge 1$ and every event $B\in\mathcal M_{j+k,\infty}$, $|P(B\mid\mathcal M_{1j})-P(B)|\le\varphi(k)$ almost surely, where $\mathcal M_{a,b}=\sigma(X_i: a\le i\le b)$. For $m\ge0$ and indices $i,j$ let $V^{(i,j)}=\sum_{|k-i|>m,\,|k-j|>m}X_k$. Then
--   $$E\bigl|V^{(i,j)}-EV^{(i,j)}\bigr|\le\bigl[\operatorname{Var}(V^{(i,j)})\bigr]^{1/2}\le\lambda^{1/2}\bigl[m+1+2(n\varphi(m+1))^{1/2}\bigr].$$
--   The first inequality is Jensen's; the second is Lemma 4.4 for the subsequence obtained by omitting the trials near $i$ and $j$, which again satisfies (4.1), with $EV^{(i,j)}\le\lambda$.
--
--   **Formalization Note** The trials are $X:\mathbb N\to\Omega\to\mathbb N$ with `IsBernoulliTrials` (measurable, zero outside $[1,n]$, at most $1$ almost surely); $p_i$ is the definition `prob`, so it cannot disagree with $X$. Constant padding variables generate the trivial $\sigma$-algebra, so (4.1) for the padded sequence is (4.1) for $X_1,\dots,X_n$. Double sums over $|i-j|$ are computed in $\mathbb Z$. $\min(\lambda^{-1/2},1)$ is `min (1 / Real.sqrt λ) 1` and $(n\varphi(m+1))^{1/2}$ is `Real.sqrt (n * φ (m + 1))`.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 541, proof of Theorem 4.2, (4.16)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem bound_4_16 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) (i j : ℕ) :
    ∫ ω, |(Vij n m X i j ω : ℝ) - ∫ ω', (Vij n m X i j ω' : ℝ) ∂P| ∂P
        ≤ Real.sqrt (Var[fun ω => (Vij n m X i j ω : ℝ); P]) ∧
      Real.sqrt (Var[fun ω => (Vij n m X i j ω : ℝ); P])
        ≤ Real.sqrt (lam P n X) * (m + 1 + 2 * Real.sqrt ((n : ℝ) * φ (m + 1))) := by sorry

end PoissonDepTrials.MixInv
