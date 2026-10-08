-- Prove2me | Theorems.Thm_RogersSatchell_Correction_second_moment_eq
-- name    : RogersSatchell.Correction.second_moment_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:36.394053+00:00
-- url     : https://prove2.me/theorems/b91f89b1-2394-42e1-a06e-bd582fba211d
-- title:
--   Eq. (12) — under law (9), E Z² = σ²h/6
-- statement:
--   Let $\sigma > 0$ and $h > 0$, and let $Z$ be a random variable on a probability space with distribution (9): $P(Z>\alpha) = G_{\sigma,h}(\alpha) = \int_0^h e^{-2\alpha^2/(u\sigma^2)}(4uh)^{-1/2}\,du$ for every $\alpha \ge 0$. Then $Z$ is square integrable and
--
--   $$E Z^2 \;=\; \frac{\sigma^2 h}{6} .$$
--
--   This is one of the two ingredients of the second moment $E[(Z\vee Z')^2] = EZ^2 + EZ'^2 - E[(Z\wedge Z')^2]$.
--
--   **Formalization Note.** The paper introduces (12) with "Recalling the distribution (7) of $Z$"; the distribution of $Z$ is (9), and (7) is the density of $t - H_x$ that enters it. Square integrability (`MemLp Z 2`) is part of the conclusion.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), p. 508, Section 3, Eq. (12)

import Mathlib
import Definitions.Def_RogersSatchell_Correction_OvershootLaw

open MeasureTheory

namespace RogersSatchell.Correction

/-- (12), §3, p. 508: if `Z` has the overshoot law (9) with `σ, h > 0`, then `Z ∈ L²` and
`E Z² = σ² h / 6`. -/
theorem second_moment_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (Z : Ω → ℝ) (hZ : HasOvershootLaw P σ h Z) :
    MemLp Z 2 P ∧ ∫ ω, Z ω ^ 2 ∂P = σ ^ 2 * h / 6 := by sorry

end RogersSatchell.Correction
