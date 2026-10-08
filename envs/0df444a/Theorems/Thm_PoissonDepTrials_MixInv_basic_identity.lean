-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_basic_identity
-- name    : PoissonDepTrials.MixInv.basic_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:39:02.842059+00:00
-- url     : https://prove2.me/theorems/11507414-64b7-4611-bf3e-50d5c16d05b8
-- title:
--   (2.2), pp. 535–536 — the basic identity for E[Wf(W) − λf(W+1)]
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, with $p_i=P(X_i=1)=1-P(X_i=0)$, padded by $X_i\equiv 0$ for $i\le 0$ and $i\ge n+1$. Write $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. Fix a nonnegative integer $m$ and any real function $f$ on the nonnegative integers. With $V^{(i)}$, $Y_{ij}$, $Y'_{ij}$ as in the setting and $\Delta f(w)=f(w+1)-f(w)$,
--   $$E[Wf(W)-\lambda f(W+1)]=\sum\sum_{0<|i-j|\le m}E\bigl[X_iX_j\,\Delta f(Y'_{i,j-1}+1)\bigr]+\sum_{i=1}^nE\bigl[(X_i-p_i)f(V^{(i)}+1)\bigr]-\sum\sum_{|i-j|\le m}p_i\,E\bigl[X_j\,\Delta f(Y_{i,j-1}+1)\bigr].$$
--   No dependence assumption is made: the identity holds for an arbitrary sequence of dependent Bernoulli trials. It is the starting point of every bound in the paper.
--
--   **Formalization Note** The trials are $X:\mathbb N\to\Omega\to\mathbb N$ with `IsBernoulliTrials` (measurable, zero outside $[1,n]$, at most $1$ almost surely); $p_i$ is the definition `prob`, so it cannot disagree with $X$. Constant padding variables generate the trivial $\sigma$-algebra, so (4.1) for the padded sequence is (4.1) for $X_1,\dots,X_n$. Double sums over $|i-j|$ are computed in $\mathbb Z$. The double sums run over $i,j\in[1,n]$, which is exact since $X_j=0$ outside $[1,n]$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), pp. 535–536, §2, (2.2)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem basic_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (m : ℕ) (f : ℕ → ℝ) :
    ∫ ω, ((W n X ω : ℝ) * f (W n X ω) - lam P n X * f (W n X ω + 1)) ∂P =
      (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P)
        + (∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P)
        - ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            prob P X i * ∫ ω, (X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P := by sorry

end PoissonDepTrials.MixInv
