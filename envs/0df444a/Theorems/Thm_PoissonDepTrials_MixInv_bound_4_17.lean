-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_bound_4_17
-- name    : PoissonDepTrials.MixInv.bound_4_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:08:37.571101+00:00
-- url     : https://prove2.me/theorems/36a9a2a3-9e99-4fac-aea7-5cad75fa9d27
-- title:
--   (4.17), proof of Theorem 4.2, p. 541 — Cov(|V^{(i,j)} − EV^{(i,j)}|, X_iX_j) ≤ 4np_iφ(m + 1) + 4λφ(m + 1)
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, with $p_i=P(X_i=1)=1-P(X_i=0)$, padded by $X_i\equiv 0$ for $i\le 0$ and $i\ge n+1$. Write $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. Assume Ibragimov's mixing condition (4.1): there is a non-increasing sequence $\varphi(k)\downarrow 0$ such that for all $j,k\ge 1$ and every event $B\in\mathcal M_{j+k,\infty}$, $|P(B\mid\mathcal M_{1j})-P(B)|\le\varphi(k)$ almost surely, where $\mathcal M_{a,b}=\sigma(X_i: a\le i\le b)$. For $m\ge0$ and indices $i,j\in[1,n]$ with $0<|i-j|\le m$,
--   $$\operatorname{Cov}\bigl(|V^{(i,j)}-EV^{(i,j)}|,\ X_iX_j\bigr)\le4np_i\varphi(m+1)+4\lambda\varphi(m+1).$$
--   This is the first and last member of the paper's chain (4.17), obtained from Lemma 4.3; the intermediate member uses an independent copy of the trials, which stays inside the proof.
--
--   **Formalization Note** The trials are $X:\mathbb N\to\Omega\to\mathbb N$ with `IsBernoulliTrials` (measurable, zero outside $[1,n]$, at most $1$ almost surely); $p_i$ is the definition `prob`, so it cannot disagree with $X$. Constant padding variables generate the trivial $\sigma$-algebra, so (4.1) for the padded sequence is (4.1) for $X_1,\dots,X_n$. Double sums over $|i-j|$ are computed in $\mathbb Z$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 541, proof of Theorem 4.2, (4.17)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem bound_4_17 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) (i j : ℕ)
    (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n)
    (hij : 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m) :
    cov[fun ω => |(Vij n m X i j ω : ℝ) - ∫ ω', (Vij n m X i j ω' : ℝ) ∂P|,
        fun ω => (X i ω : ℝ) * X j ω; P]
      ≤ 4 * n * prob P X i * φ (m + 1) + 4 * lam P n X * φ (m + 1) := by sorry

end PoissonDepTrials.MixInv
