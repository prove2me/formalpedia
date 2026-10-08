-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_variance_identity_4_7
-- name    : PoissonDepTrials.MixSqrt.variance_identity_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:15.204027+00:00
-- url     : https://prove2.me/theorems/a5ab1431-96b8-4815-ba90-757ffc74dc1b
-- title:
--   (4.7), p. 540 — Var(W) = λ + ΣΣ_{0<|i−j|≤m} EX_iX_j − ΣΣ_{|i−j|≤m} p_ip_j + Σ_i E[(X_i − p_i)V^{(i)}]
-- statement:
--   Let $X_1,\dots,X_n$ be Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, possibly dependent, with $p_i=P(X_i=1)$, and put $W=\sum_{i=1}^n X_i$ and $\lambda=\sum_{i=1}^n p_i$. As on p. 535, $X_i$ is taken to be identically zero when $i\le 0$ or $i\ge n+1$. Fix $m\ge0$. Then
--   $$\operatorname{Var}(W)=\lambda+\sum\sum_{0<|i-j|\le m}EX_iX_j-\sum\sum_{|i-j|\le m}p_ip_j+\sum_{i=1}^nE\bigl[(X_i-p_i)V^{(i)}\bigr].$$
--   No assumption on the dependence is made; the identity is (2.2) with $f(w)=w$.
--
--   It is the first step of the proofs of Lemmas 4.4 and 4.5: it expresses the local correlation sum $\sum\sum_{0<|i-j|\le m}EX_iX_j$ through $\operatorname{Var}(W)$, which is what lets the final bound be stated in terms of $\operatorname{Var}(W)-\lambda$.
--
--   **Formalization Note** The trials are a sequence $X:\mathbb N\to\Omega\to\mathbb N$ that is measurable, almost surely $\{0,1\}$-valued, and identically $0$ at index $0$ and above $n$ (the paper's padding convention, which changes no $\sigma$-algebra). $p_i$ is defined as $P(X_i=1)$, not a free parameter.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 540, proof of Lemma 4.4, (4.7)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), proof of Lemma 4.4, p. 540, (4.7): for an arbitrary sequence of dependent
Bernoulli trials,
`Var(W) = λ + ΣΣ_{0<|i−j|≤m} EX_iX_j − ΣΣ_{|i−j|≤m} p_ip_j + Σ_i E[(X_i − p_i)V^{(i)}]`. -/
theorem variance_identity_4_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (m : ℕ) :
    Var[fun ω => (W n X ω : ℝ); P] = lam P n X
      + (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω ∂P)
      - (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * prob P X j)
      + ∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) ∂P := by sorry

end PoissonDepTrials.MixSqrt
