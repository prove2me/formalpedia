-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_3_14
-- name    : SKHessianAscent.lemma_3_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:09:20.854589+00:00
-- url     : https://prove2.me/theorems/db2b69ed-431d-4e06-90b2-66162bfbbea8
-- title:
--   Lemma 3.14 — indicator-weighted centered exponential moments: $\mathbf E[\mathbf 1_S e^{\lambda(F-\mathbf E[F\mid S])}]\le e^{2v\lambda^2}$
-- statement:
--   Let $F$ be a real integrable random variable on a probability space $(\Omega,P)$ and let $v>0$. Suppose $F$ is sub-Gaussian around its mean with variance proxy $v$:
--
--   $$
--   \mathbf E\big[e^{s(F-\mathbf E[F])}\big]\le e^{vs^2/2}\qquad\text{for all }s\in\mathbb R .
--   $$
--
--   Then for every event $S$ and every $\lambda\in\mathbb R$,
--
--   $$
--   \mathbf E\big[\mathbf 1_S\,e^{\lambda(F-\mathbf E[F\mid S])}\big]\le e^{2v\lambda^2},
--   $$
--
--   where $\mathbf E[F\mid S]=\mathbf E[F\mathbf 1_S]/P(S)$. If $P(S)=0$ the left-hand side is zero.
--
--   In the paper this removes the paths that leave the safe set from the sub-Gaussian bound on the Jarzynski weights (Corollary 3.15).
--
--   **Formalization Note** Both expectations of exponentials are written as lower Lebesgue integrals in $[0,\infty]$, so the hypothesis includes finiteness of the moment generating function. When $P(S)=0$ the integral over $S$ is $0$, so that case needs no separate convention.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma 3.14, p. 16

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SKHessianAscent

theorem lemma_3_14 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (hF : Integrable F P) (v : ℝ) (hv : 0 < v)
    (hmgf : ∀ s : ℝ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (s * (F ω - ∫ x, F x ∂P))) ∂P ≤
        ENNReal.ofReal (Real.exp (v * s ^ 2 / 2)))
    (S : Set Ω) (hS : MeasurableSet S) (lam : ℝ) :
    ∫⁻ ω in S, ENNReal.ofReal (Real.exp (lam * (F ω - (∫ x in S, F x ∂P) / (P S).toReal))) ∂P ≤
      ENNReal.ofReal (Real.exp (2 * v * lam ^ 2)) := by sorry

end SKHessianAscent
