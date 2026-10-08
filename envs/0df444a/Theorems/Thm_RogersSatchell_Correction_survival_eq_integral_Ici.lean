-- Prove2me | Theorems.Thm_RogersSatchell_Correction_survival_eq_integral_Ici
-- name    : RogersSatchell.Correction.survival_eq_integral_Ici
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:07.784996+00:00
-- url     : https://prove2.me/theorems/354c388e-e2f1-46f7-a03e-4f77487c8662
-- title:
--   Eq. (9) — the two integral forms of the overshoot survival function agree
-- statement:
--   Let $\sigma > 0$, $h > 0$ and $\alpha \ge 0$. Both integrals below converge absolutely, and
--
--   $$\int_0^h e^{-2\alpha^2/(u\sigma^2)}\,\frac{du}{(4uh)^{1/2}} \;=\; \int_{h^{-1}}^\infty e^{-2\alpha^2 s/\sigma^2}\,\frac{ds}{(4hs^3)^{1/2}} .$$
--
--   The left side is the survival function $G_{\sigma,h}(\alpha)$ of the overshoot law (9). The right side is the third line of (9), and it is the form in which the paper computes every moment in (10), (12) and (13) and the mean of $Z\wedge Z'$.
--
--   **Formalization Note.** The left integral is over $(0,h]$, the right one over $[h^{-1},\infty)$; endpoints carry no mass. The statement asserts integrability of both integrands as well as the equality, so that neither side can be a junk value of the Bochner integral.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), p. 507, Section 3, Eq. (9)

import Mathlib
import Definitions.Def_RogersSatchell_Correction_OvershootLaw

open MeasureTheory

namespace RogersSatchell.Correction

/-- (9), §3, p. 507: the substitution `s = 1/u` turns the second line of (9) into the third:
for `σ, h > 0` and `α ≥ 0`, both integrands are integrable and
`∫_{(0,h]} e^{-2α²/(uσ²)} (4uh)^{-1/2} du = ∫_{[h⁻¹,∞)} e^{-2α²s/σ²} (4hs³)^{-1/2} ds`. -/
theorem survival_eq_integral_Ici (σ h α : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hα : 0 ≤ α) :
    IntegrableOn
        (fun u : ℝ => Real.exp (-2 * α ^ 2 / (u * σ ^ 2)) * (4 * u * h) ^ (-(1 / 2 : ℝ)))
        (Set.Ioc 0 h) ∧
      IntegrableOn
        (fun s : ℝ => Real.exp (-2 * α ^ 2 * s / σ ^ 2) * (4 * h * s ^ 3) ^ (-(1 / 2 : ℝ)))
        (Set.Ici h⁻¹) ∧
      overshootSurvival σ h α =
        ∫ s in Set.Ici h⁻¹, Real.exp (-2 * α ^ 2 * s / σ ^ 2) * (4 * h * s ^ 3) ^ (-(1 / 2 : ℝ)) := by sorry

end RogersSatchell.Correction
