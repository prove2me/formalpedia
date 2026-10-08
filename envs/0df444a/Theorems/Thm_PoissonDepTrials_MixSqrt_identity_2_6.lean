-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_identity_2_6
-- name    : PoissonDepTrials.MixSqrt.identity_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:37:48.505859+00:00
-- url     : https://prove2.me/theorems/4ed84b91-db50-470b-98f7-23696821f643
-- title:
--   (2.6), p. 536 — Eh(W) = 𝒫_λh + three error terms in ΔS_λh and S_λh
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, possibly dependent, with $p_i=P(X_i=1)$, and put $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. As on p. 535, $X_i$ is taken to be identically zero when $i\le 0$ or $i\ge n+1$.
--
--   Assume $\lambda>0$, fix a nonnegative integer $m$, and let $h$ be a bounded real function on the nonnegative integers with Stein solution $S_\lambda h$ (2.5). Then
--   $$
--   \begin{aligned}
--   Eh(W)&=\mathcal P_\lambda h+\sum\sum_{0<|i-j|\le m}E\bigl[X_iX_j\,\Delta S_\lambda h(Y'_{i,j-1}+1)\bigr]
--   +\sum_{i=1}^nE\bigl[(X_i-p_i)S_\lambda h(V^{(i)}+1)\bigr]\\
--   &\quad-\sum\sum_{|i-j|\le m}p_i\,E\bigl[X_j\,\Delta S_\lambda h(Y_{i,j-1}+1)\bigr].
--   \end{aligned}
--   $$
--   No assumption on the dependence between the trials is made.
--
--   The identity reduces the Poisson approximation problem to bounding the three error terms on the right, which is what §§3–4 do.
--
--   **Formalization Note** The trials are a sequence $X:\mathbb N\to\Omega\to\mathbb N$ that is measurable, almost surely $\{0,1\}$-valued, and identically $0$ at index $0$ and above $n$ (the paper's padding convention, which changes no $\sigma$-algebra). $p_i$ is defined as $P(X_i=1)$, not a free parameter. The hypothesis $\lambda>0$ is implicit on the page ($S_\lambda h$ divides by $\lambda^w$). Boundedness of $h$ is given as $|h|\le M$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 536, §2, (2.6)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), §2, p. 536, (2.6): substituting `f = S_λh` into (2.2),
`Eh(W) = 𝒫_λh + ΣΣ_{0<|i−j|≤m} E[X_iX_jΔS_λh(Y'_{i,j−1} + 1)]
  + Σ_i E[(X_i − p_i)S_λh(V^{(i)} + 1)] − ΣΣ_{|i−j|≤m} p_i E[X_jΔS_λh(Y_{i,j−1} + 1)]`,
for an arbitrary sequence of dependent Bernoulli trials with `λ > 0` and bounded `h`. -/
theorem identity_2_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hlam : 0 < lam P n X) (m : ℕ) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    ∫ ω, h (W n X ω) ∂P = poissonExp (lam P n X) h
      + (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω * delta (stein (lam P n X) h) (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P)
      + (∑ i ∈ Finset.Icc 1 n,
          ∫ ω, ((X i ω : ℝ) - prob P X i) * stein (lam P n X) h (V n m X i ω + 1) ∂P)
      - ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ∫ ω, (X j ω : ℝ) * delta (stein (lam P n X) h) (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P := by sorry

end PoissonDepTrials.MixSqrt
