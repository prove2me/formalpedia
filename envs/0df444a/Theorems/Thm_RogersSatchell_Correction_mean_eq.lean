-- Prove2me | Theorems.Thm_RogersSatchell_Correction_mean_eq
-- name    : RogersSatchell.Correction.mean_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:06.46078+00:00
-- url     : https://prove2.me/theorems/d6f7db72-4cc8-4b17-88bc-d588c98a8d18
-- title:
--   Eq. (10) — under law (9), E Z = σ(2πh)^{1/2}/8
-- statement:
--   Let $\sigma > 0$ and $h > 0$, and let $Z$ be a random variable on a probability space with distribution (9), that is $P(Z>\alpha) = G_{\sigma,h}(\alpha) = \int_0^h e^{-2\alpha^2/(u\sigma^2)}(4uh)^{-1/2}\,du$ for every $\alpha \ge 0$. Then $Z$ is integrable and
--
--   $$E Z \;=\; \frac{\sigma\,(2\pi h)^{1/2}}{8} .$$
--
--   In the paper this is the conditional mean $E(Z \mid t-h<H_x<t,\ X_t=x)$ of the overshoot of the continuous maximum over the sampled one on the left of the sampling time; under the modelling assumption (9) it is an exact identity about the law. It is one of the two terms in $E(Z\vee Z') = EZ + EZ' - E(Z\wedge Z')$.
--
--   **Formalization Note.** The conditioning in the paper's (10) is the modelling context of the law (9), not a hypothesis here. Integrability of $Z$ is part of the conclusion.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), p. 508, Section 3, Eq. (10)

import Mathlib
import Definitions.Def_RogersSatchell_Correction_OvershootLaw

open MeasureTheory

namespace RogersSatchell.Correction

/-- (10), §3, p. 508: if `Z` has the overshoot law (9) with `σ, h > 0`, then `Z` is integrable
and `E Z = σ (2πh)^{1/2} / 8`. -/
theorem mean_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (Z : Ω → ℝ) (hZ : HasOvershootLaw P σ h Z) :
    Integrable Z P ∧ ∫ ω, Z ω ∂P = σ * Real.sqrt (2 * Real.pi * h) / 8 := by sorry

end RogersSatchell.Correction
