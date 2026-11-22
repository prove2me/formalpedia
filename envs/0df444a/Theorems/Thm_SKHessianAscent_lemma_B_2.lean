-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_B_2
-- name    : SKHessianAscent.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:43:32.530747+00:00
-- url     : https://prove2.me/theorems/668317db-2418-4b56-8c1f-ccd445d00ef0
-- title:
--   Lemma B.2 — spectral self-stability $\rho(\beta^2\mathcal M)<1$ for $\beta<1$
-- statement:
--   Let $Y^*$ be a real random variable, $T=\tanh(Y^*)\in[-1,1]$, and $\mu_r=\mathbf E[T^r]$ for $r\in\{1,2,3,4\}$. Define
--
--   $$
--   \mathcal M=\begin{pmatrix}1-4\mu_2+3\mu_4 & 2(\mu_1-\mu_3)\\ \mu_3-\mu_1 & 1-\mu_2\end{pmatrix}.
--   $$
--
--   Then for every $0\le\beta<1$ the spectral radius satisfies
--
--   $$
--   \rho(\beta^2\mathcal M)<1 .
--   $$
--
--   This is the self-stability condition under which the cavity estimates of the earlier paper of the series (arXiv:2605.03718, §5) extend from $\beta<1/2$ to all $\beta<1$.
--
--   **Formalization Note** The spectral radius is that of the $2\times2$ matrix over $\mathbb C$ (complex eigenvalues are included). The paper writes "for every $\beta<1$"; $\beta$ is an inverse temperature and the statement is posed for $0\le\beta<1$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma B.2, p. 48

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SKHessianAscent

theorem lemma_B_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    let μ : ℕ → ℝ := fun r => ∫ ω, Real.tanh (Y ω) ^ r ∂P
    let M : Matrix (Fin 2) (Fin 2) ℂ :=
      !![((1 - 4 * μ 2 + 3 * μ 4 : ℝ) : ℂ), ((2 * (μ 1 - μ 3) : ℝ) : ℂ);
         ((μ 3 - μ 1 : ℝ) : ℂ), ((1 - μ 2 : ℝ) : ℂ)]
    spectralRadius ℂ (((β ^ 2 : ℝ) : ℂ) • M) < 1 := by sorry

end SKHessianAscent
