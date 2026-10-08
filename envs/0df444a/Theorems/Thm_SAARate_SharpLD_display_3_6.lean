-- Prove2me | Theorems.Thm_SAARate_SharpLD_display_3_6
-- name    : SAARate.SharpLD.display_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:06.532375+00:00
-- url     : https://prove2.me/theorems/bad3f6b4-4c2d-4fae-a392-04df9f534954
-- title:
--   (3.6), p. 10 — I(z) ≥ sup_d sup_t [t z(d) − log M_d(t)] = sup_d I_d(z(d))
-- statement:
--   Let $P$ be a probability measure on $(\Omega,\mathcal F)$ and $h:\mathbb R^m\times\Omega\to\mathbb R$ with $h(\cdot,\omega)$ convex for every $\omega$; fix $\bar x\in\mathbb R^m$. Let $Z=C(S^{m-1})$ with the sup norm and regard $\eta(\cdot,\omega)=h'_\omega(\bar x,\cdot)$ restricted to the unit sphere as a random element of $Z$. Let $I$ be its rate function (3.4),
--   $$I(z)=\sup_{z^*\in Z^*}\{z^*(z)-\log M(z^*)\},\qquad M(z^*)=\mathbb E_P\,e^{z^*(\eta(\cdot,\omega))},$$
--   and for $d\in S^{m-1}$ let $M_d(t)=\mathbb E_P\,e^{t\eta(d,\omega)}$ and $I_d(\alpha)=\sup_{t\in\mathbb R}[t\alpha-\log M_d(t)]$ (3.5). Then for every $z\in Z$
--   $$I(z)\ \ge\ \sup_{d\in S^{m-1}}\ \sup_{t\in\mathbb R}\,\bigl[t z(d)-\log M_d(t)\bigr]\ =\ \sup_{d\in S^{m-1}}I_d(z(d)).$$
--
--   This links the infinite-dimensional rate function of Cramér's theorem in $Z$ with the one-dimensional rate functions of the evaluations $z\mapsto z(d)$.
--
--   **Formalization Note** All suprema are taken in the extended reals; $\log M$ and $\log M_d$ are the published `logMGF` (with values in $(-\infty,+\infty]$), and $I_d$ is the published `legendre`. Convexity of $h(\cdot,\omega)$ is assumed so that $\eta(\cdot,\omega)$ is continuous on the sphere and is a genuine element of $Z$ (see the Setting file).
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 10, (3.4), (3.5), (3.6)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_SAARate_SharpLD_Setting

open MeasureTheory ProbabilityTheory Filter Topology BellWilliams2001.ThresholdPolicy

namespace SAARate.SharpLD

theorem display_3_6 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : SAARate.Sharp.E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (xbar : SAARate.Sharp.E m) (z : Z m) :
    (⨆ d : Metric.sphere (0 : SAARate.Sharp.E m) 1, ⨆ t : ℝ,
        ((t * z d : ℝ) : EReal) - logMGF P (eta h xbar (d : SAARate.Sharp.E m)) t) ≤
      cramerRate P (etaZ h xbar) z ∧
    (⨆ d : Metric.sphere (0 : SAARate.Sharp.E m) 1, ⨆ t : ℝ,
        ((t * z d : ℝ) : EReal) - logMGF P (eta h xbar (d : SAARate.Sharp.E m)) t) =
      ⨆ d : Metric.sphere (0 : SAARate.Sharp.E m) 1, legendre (logMGF P (eta h xbar (d : SAARate.Sharp.E m))) (z d) := by sorry

end SAARate.SharpLD
