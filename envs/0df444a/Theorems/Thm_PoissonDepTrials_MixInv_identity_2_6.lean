-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_identity_2_6
-- name    : PoissonDepTrials.MixInv.identity_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:39:48.794755+00:00
-- url     : https://prove2.me/theorems/5a387108-aa23-4bc5-acce-4cd78b205d29
-- title:
--   (2.6), p. 536 — Eh(W) = 𝒫_λh + the three error terms in S_λh
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, with $p_i=P(X_i=1)=1-P(X_i=0)$, padded by $X_i\equiv 0$ for $i\le 0$ and $i\ge n+1$. Write $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. Assume $\lambda>0$, fix $m\ge0$ and a bounded $h$. Then
--   $$Eh(W)=\mathcal P_\lambda h+\sum\sum_{0<|i-j|\le m}E\bigl[X_iX_j\,\Delta S_\lambda h(Y'_{i,j-1}+1)\bigr]+\sum_{i=1}^nE\bigl[(X_i-p_i)S_\lambda h(V^{(i)}+1)\bigr]-\sum\sum_{|i-j|\le m}p_iE\bigl[X_j\,\Delta S_\lambda h(Y_{i,j-1}+1)\bigr].$$
--   This is the basic identity (2.2) with $f=S_\lambda h$; bounding its three error terms proves Theorems 4.1 and 4.2.
--
--   **Formalization Note** The trials are $X:\mathbb N\to\Omega\to\mathbb N$ with `IsBernoulliTrials` (measurable, zero outside $[1,n]$, at most $1$ almost surely); $p_i$ is the definition `prob`, so it cannot disagree with $X$. Constant padding variables generate the trivial $\sigma$-algebra, so (4.1) for the padded sequence is (4.1) for $X_1,\dots,X_n$. Double sums over $|i-j|$ are computed in $\mathbb Z$. $\lambda>0$ is required for $S_\lambda h$ to be defined and is stated; boundedness of $h$ is a bound $M$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 536, (2.6)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem identity_2_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hlam : 0 < lam P n X) (m : ℕ) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    ∫ ω, h (W n X ω) ∂P = poissonExp (lam P n X) h
      + (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω *
            delta (stein (lam P n X) h) (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P)
      + (∑ i ∈ Finset.Icc 1 n,
          ∫ ω, ((X i ω : ℝ) - prob P X i) * stein (lam P n X) h (V n m X i ω + 1) ∂P)
      - ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
          prob P X i * ∫ ω, (X j ω : ℝ) *
            delta (stein (lam P n X) h) (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P := by sorry

end PoissonDepTrials.MixInv
