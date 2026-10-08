-- Prove2me | Theorems.Thm_SAARate_SharpLD_display_3_12
-- name    : SAARate.SharpLD.display_3_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:12.860045+00:00
-- url     : https://prove2.me/theorems/7341a3af-d38d-474a-8224-6d6836748c99
-- title:
--   (3.12), p. 11 — |Λ′(t) − Λ′(s)| ≤ κ²|t − s|
-- statement:
--   Let $X$ be a real random variable on a probability space $(\Omega,\mathcal F,P)$ with $|X|\le\kappa$ almost surely, and let $\Lambda(t)=\log\mathbb E[e^{tX}]$. Then for all $t,s\in\mathbb R$
--   $$|\Lambda'(t)-\Lambda'(s)|\le\kappa^2|t-s| .$$
--
--   The derivative of the cumulant generating function of a variable bounded by $\kappa$ is Lipschitz with constant $\kappa^2$. By convex duality this is equivalent to strong convexity of the conjugate $\Lambda^*$ with modulus $1/\kappa^2$, used for (3.13).
--
--   **Formalization Note** $\Lambda$ is Mathlib's `cgf`, $\Lambda'$ is `deriv`; the statement is made for an arbitrary bounded measurable $X$.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 11, proof of Theorem 3.1, (3.12)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace SAARate.SharpLD

theorem display_3_12 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (κ : ℝ)
    (hXκ : ∀ᵐ ω ∂P, |X ω| ≤ κ) :
    ∀ t s : ℝ, |deriv (cgf X P) t - deriv (cgf X P) s| ≤ κ ^ 2 * |t - s| := by sorry

end SAARate.SharpLD
