-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_lemma_4_5
-- name    : PoissonDepTrials.MixInv.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:22:55.50399+00:00
-- url     : https://prove2.me/theorems/5ebd2628-2f1e-4882-9390-7fafbab4c487
-- title:
--   Lemma 4.5, p. 540 — ΣΣ_{0<|i−j|≤m} EX_iX_j ≤ Var W − λ + (2m + 1)Σp_i² + 4λnφ(m + 1)
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, with $p_i=P(X_i=1)=1-P(X_i=0)$, padded by $X_i\equiv 0$ for $i\le 0$ and $i\ge n+1$. Write $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. Assume Ibragimov's mixing condition (4.1): there is a non-increasing sequence $\varphi(k)\downarrow 0$ such that for all $j,k\ge 1$ and every event $B\in\mathcal M_{j+k,\infty}$, $|P(B\mid\mathcal M_{1j})-P(B)|\le\varphi(k)$ almost surely, where $\mathcal M_{a,b}=\sigma(X_i: a\le i\le b)$. For every $m\ge0$,
--   $$\sum\sum_{0<|i-j|\le m}EX_iX_j\le\operatorname{Var}(W)-\lambda+(2m+1)\sum_{i=1}^np_i^2+4\lambda n\varphi(m+1).$$
--   It expresses the local dependence of the trials through the variance of $W$, which turns the bounds of (4.18)–(4.19) into the variance form of Theorem 4.2.
--
--   **Formalization Note** The trials are $X:\mathbb N\to\Omega\to\mathbb N$ with `IsBernoulliTrials` (measurable, zero outside $[1,n]$, at most $1$ almost surely); $p_i$ is the definition `prob`, so it cannot disagree with $X$. Constant padding variables generate the trivial $\sigma$-algebra, so (4.1) for the padded sequence is (4.1) for $X_1,\dots,X_n$. Double sums over $|i-j|$ are computed in $\mathbb Z$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 540, Lemma 4.5, (4.9)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem lemma_4_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
        ∫ ω, (X i ω : ℝ) * X j ω ∂P
      ≤ Var[fun ω => (W n X ω : ℝ); P] - lam P n X
        + (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2
        + 4 * lam P n X * n * φ (m + 1) := by sorry

end PoissonDepTrials.MixInv
