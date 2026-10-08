-- Prove2me | Theorems.Thm_SAARate_SharpLD_display_3_11
-- name    : SAARate.SharpLD.display_3_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:11.159869+00:00
-- url     : https://prove2.me/theorems/4256a7be-028d-430e-9b6a-417f679b4169
-- title:
--   (3.11), p. 11 — |Λ″(t)| = |E[X²e^{tX}]/E[e^{tX}] − Λ′(t)²| ≤ |κ² − Λ′(t)²| ≤ κ²
-- statement:
--   Let $X$ be a real random variable on a probability space $(\Omega,\mathcal F,P)$ with $|X|\le\kappa$ almost surely, and let $\Lambda(t)=\log\mathbb E[e^{tX}]$. Then for every $t\in\mathbb R$
--   $$|\Lambda''(t)|=\left|\frac{\mathbb E[X^2e^{tX}]}{\mathbb E[e^{tX}]}-(\Lambda'(t))^2\right|\le|\kappa^2-(\Lambda'(t))^2|\le\kappa^2 .$$
--
--   The second derivative of the cumulant generating function is the variance of $X$ under the exponentially tilted law, and (3.11) bounds it by $\kappa^2$. Through (3.12) this makes $\Lambda'$ Lipschitz with constant $\kappa^2$, which is what gives the conjugate $I_d=\Lambda^*$ strong convexity modulus $1/\kappa^2$.
--
--   **Formalization Note** The statement is the conjunction of the identity $\Lambda''(t)=\mathbb E[X^2e^{tX}]/\mathbb E[e^{tX}]-(\Lambda'(t))^2$ and the two printed inequalities; $\Lambda$ is Mathlib's `cgf` and $\Lambda'$, $\Lambda''$ are iterated `deriv`. It is stated for an arbitrary bounded measurable $X$.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 11, proof of Theorem 3.1, (3.11)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace SAARate.SharpLD

theorem display_3_11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (κ : ℝ)
    (hXκ : ∀ᵐ ω ∂P, |X ω| ≤ κ) :
    ∀ t : ℝ,
      deriv (deriv (cgf X P)) t =
          (∫ ω, X ω ^ 2 * Real.exp (t * X ω) ∂P) / mgf X P t - (deriv (cgf X P) t) ^ 2 ∧
        |(∫ ω, X ω ^ 2 * Real.exp (t * X ω) ∂P) / mgf X P t - (deriv (cgf X P) t) ^ 2| ≤
          |κ ^ 2 - (deriv (cgf X P) t) ^ 2| ∧
        |κ ^ 2 - (deriv (cgf X P) t) ^ 2| ≤ κ ^ 2 := by sorry

end SAARate.SharpLD
