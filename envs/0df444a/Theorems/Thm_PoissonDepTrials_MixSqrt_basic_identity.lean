-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_basic_identity
-- name    : PoissonDepTrials.MixSqrt.basic_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:37:39.191977+00:00
-- url     : https://prove2.me/theorems/5c9d2a7d-210e-42ae-bb1a-901f1614eaf5
-- title:
--   (2.2), pp. 535–536 — the basic identity for E[Wf(W) − λf(W + 1)]
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, possibly dependent, with $p_i=P(X_i=1)$, and put $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. As on p. 535, $X_i$ is taken to be identically zero when $i\le 0$ or $i\ge n+1$.
--
--   Fix a nonnegative integer $m$ and let $V^{(i)}$, $Y_{ij}$, $Y'_{ij}$ and $\Delta$ be as in the setting. Then for **every** real-valued function $f$ on the nonnegative integers,
--   $$
--   \begin{aligned}
--   E\bigl[Wf(W)-\lambda f(W+1)\bigr]
--   &=\sum\sum_{0<|i-j|\le m}E\bigl[X_iX_j\,\Delta f(Y'_{i,j-1}+1)\bigr]
--   +\sum_{i=1}^nE\bigl[(X_i-p_i)f(V^{(i)}+1)\bigr]\\
--   &\quad-\sum\sum_{|i-j|\le m}p_i\,E\bigl[X_j\,\Delta f(Y_{i,j-1}+1)\bigr].
--   \end{aligned}
--   $$
--   No assumption on the dependence between the trials is made.
--
--   This is the identity from which the whole method starts: choosing $f$ as the solution of the Stein equation turns its left side into $Eh(W)-\mathcal P_\lambda h$, and choosing $f(w)=w$ gives the variance identity (4.7).
--
--   **Formalization Note** The trials are a sequence $X:\mathbb N\to\Omega\to\mathbb N$ that is measurable, almost surely $\{0,1\}$-valued, and identically $0$ at index $0$ and above $n$ (the paper's padding convention, which changes no $\sigma$-algebra). $p_i$ is defined as $P(X_i=1)$, not a free parameter. The double sums run over $i,j\in\{1,\dots,n\}$; terms with $j$ outside this range vanish because $X_j=0$ there. Index differences are computed in $\mathbb Z$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), pp. 535–536, §2, identity (2.2) (derived from (2.1))

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), §2, pp. 535–536, the basic identity (2.2). For an arbitrary sequence of
dependent Bernoulli trials and every real function `f` on the nonnegative integers,
`E[Wf(W) − λf(W + 1)] = ΣΣ_{0<|i−j|≤m} E[X_iX_jΔf(Y'_{i,j−1} + 1)]
  + Σ_i E[(X_i − p_i)f(V^{(i)} + 1)] − ΣΣ_{|i−j|≤m} p_i E[X_jΔf(Y_{i,j−1} + 1)]`. -/
theorem basic_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (m : ℕ) (f : ℕ → ℝ) :
    ∫ ω, ((W n X ω : ℝ) * f (W n X ω) - lam P n X * f (W n X ω + 1)) ∂P =
      (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P)
      + (∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P)
      - ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ∫ ω, (X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P := by sorry

end PoissonDepTrials.MixSqrt
