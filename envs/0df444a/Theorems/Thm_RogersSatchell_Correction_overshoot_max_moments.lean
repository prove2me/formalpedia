-- Prove2me | Theorems.Thm_RogersSatchell_Correction_overshoot_max_moments
-- name    : RogersSatchell.Correction.overshoot_max_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:57.273534+00:00
-- url     : https://prove2.me/theorems/7111416b-17e0-461a-ae88-9d2cea5314db
-- title:
--   Eq. (11) and p. 509 — for independent Z, Z′ with law (9), E(Z ∨ Z′) = aσ√h and E[(Z ∨ Z′)²] = bσ²h
-- statement:
--   Let $\sigma > 0$ and $h > 0$, and let $Z$ and $Z'$ be independent random variables on a probability space, each with the overshoot law (9):
--
--   $$P(Z>\alpha) = P(Z'>\alpha) = \int_0^h e^{-2\alpha^2/(u\sigma^2)}\,\frac{du}{(4uh)^{1/2}}\qquad(\alpha\ge0).$$
--
--   Then $Z\vee Z' = \max(Z,Z')$ and $(Z\vee Z')^2$ are integrable, and
--
--   $$E(Z\vee Z') \;=\; a\,\sigma\sqrt h,\qquad E\big[(Z\vee Z')^2\big] \;=\; b\,\sigma^2 h,$$
--
--   where $a = \sqrt{2\pi}\,\big[\tfrac14 - \tfrac{\sqrt2-1}{6}\big]$ and $b = (1 + 3\pi/4)/12$ are the constants of p. 507. Equivalently, $E(Z\vee Z') = \sigma\sqrt{2\pi h}\,[\tfrac14 - \tfrac{\sqrt2-1}{6}]$ (Eq. (11)) and $E[(Z\vee Z')^2] = \tfrac{\sigma^2 h}{12}\{1 + \tfrac{3\pi}{4}\}$.
--
--   In Rogers and Satchell's correction of the high–low variance estimator for discrete sampling at mesh $h$, $Z\vee Z'$ models the amount $\Delta$ by which the sampled maximum underestimates the maximum of the continuous log-price path, and these two moments are the coefficients that enter the corrected estimator (5).
--
--   **Formalization Note.** The law (9) and the independence of $Z$ and $Z'$ are the paper's modelling assumptions for the overshoot (p. 508); the conditioning on $t-h<H_x<t$, $X_t=x$ under which the paper derives (9) is context, not a hypothesis. The paper's approximate statements $E\Delta \doteq a\sigma\sqrt h$, $E\Delta^2 \doteq b\sigma^2h$ about the random walk are not formalized; this theorem is the exact computation for the model. Integrability of both $Z\vee Z'$ and its square is part of the conclusion.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), p. 508, Section 3, Eq. (11), and p. 509, Section 3, display following (13); constants a, b on p. 507

import Mathlib
import Definitions.Def_RogersSatchell_Correction_OvershootLaw
import Definitions.Def_RogersSatchell_Correction_Constants

open MeasureTheory ProbabilityTheory

namespace RogersSatchell.Correction

/-- (11), §3, p. 508, and the second-moment display of p. 509: if `Z, Z'` are independent, each
with the overshoot law (9) (`σ, h > 0`), then `Z ∨ Z'` and `(Z ∨ Z')²` are integrable,
`E(Z ∨ Z') = a σ √h` and `E[(Z ∨ Z')²] = b σ² h`, with `a = √(2π)[1/4 − (√2 − 1)/6]` and
`b = (1 + 3π/4)/12` the constants of p. 507. -/
theorem overshoot_max_moments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (Z Z' : Ω → ℝ)
    (hZ : HasOvershootLaw P σ h Z) (hZ' : HasOvershootLaw P σ h Z') (hind : IndepFun Z Z' P) :
    Integrable (fun ω => max (Z ω) (Z' ω)) P ∧
      Integrable (fun ω => max (Z ω) (Z' ω) ^ 2) P ∧
      ∫ ω, max (Z ω) (Z' ω) ∂P = constA * σ * Real.sqrt h ∧
      ∫ ω, max (Z ω) (Z' ω) ^ 2 ∂P = constB * σ ^ 2 * h := by sorry

end RogersSatchell.Correction
