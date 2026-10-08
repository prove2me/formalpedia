-- Prove2me | Theorems.Thm_SAARate_SharpLD_display_3_13
-- name    : SAARate.SharpLD.display_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:24.182433+00:00
-- url     : https://prove2.me/theorems/c76c91ad-be7b-483f-b4f4-1a54479875f5
-- title:
--   (3.13), p. 12 — I_d(α) ≥ (1/(2κ²))|α − ᾱ_d|²
-- statement:
--   Let $X$ be a real random variable on a probability space $(\Omega,\mathcal F,P)$, let $\kappa>0$, and suppose $|X|\le\kappa$ almost surely. Let $\Lambda(t)=\log\mathbb E[e^{tX}]$ and let
--   $$I(\alpha)=\sup_{t\in\mathbb R}\,[t\alpha-\Lambda(t)]\in[0,+\infty]$$
--   be the rate function (Cramér transform) of $X$, as in (3.5). With $\bar\alpha=\mathbb E[X]$,
--   $$I(\alpha)\ge\frac{1}{2\kappa^2}\,|\alpha-\bar\alpha|^2\qquad\text{for all }\alpha\in\mathbb R .$$
--
--   In the paper $X=\eta(d,\omega)$ for a direction $d\in T_\Theta(\bar x)\cap S^{m-1}$, $I=I_d$, and $\bar\alpha=\bar\alpha_d=f'(\bar x,d)$. The quadratic lower bound is what turns the sharpness constant $c$ into the exponential rate $c^2/(2\kappa^2)$.
--
--   **Formalization Note** $I$ is the published extended-real Legendre transform `legendre` of the extended-real log-MGF `logMGF`; for $|\alpha|>\kappa$ one has $I(\alpha)=+\infty$ and the inequality is the page's statement there, not a junk case. The statement is made for an arbitrary bounded measurable $X$.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 12, proof of Theorem 3.1, (3.5), (3.13)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation

open MeasureTheory ProbabilityTheory Filter Topology BellWilliams2001.ThresholdPolicy

namespace SAARate.SharpLD

theorem display_3_13 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (κ : ℝ) (hκ : 0 < κ)
    (hXκ : ∀ᵐ ω ∂P, |X ω| ≤ κ) :
    ∀ α : ℝ, (((1 / (2 * κ ^ 2)) * |α - ∫ ω, X ω ∂P| ^ 2 : ℝ) : EReal) ≤
      legendre (logMGF P X) α := by sorry

end SAARate.SharpLD
