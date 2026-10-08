-- Prove2me | Theorems.Thm_RogersSatchell_Correction_mean_min_eq
-- name    : RogersSatchell.Correction.mean_min_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:12.164824+00:00
-- url     : https://prove2.me/theorems/7d5cb165-8e14-4754-ae8e-7ce593c99181
-- title:
--   Section 3, p. 508 — for independent Z, Z′ with law (9), E(Z ∧ Z′) = √(2πh)(√2 − 1)σ/6
-- statement:
--   Let $\sigma > 0$ and $h > 0$, and let $Z$ and $Z'$ be independent random variables on a probability space, each with distribution (9): $P(Z>\alpha) = P(Z'>\alpha) = G_{\sigma,h}(\alpha)$ for every $\alpha \ge 0$. Then $Z\wedge Z' = \min(Z,Z')$ is integrable and
--
--   $$E(Z\wedge Z') \;=\; \frac{\sqrt{2\pi h}\,(\sqrt2 - 1)\,\sigma}{6} .$$
--
--   Together with (10) this gives (11), the mean of $Z\vee Z'$, which is the paper's approximation of the amount by which the sampled maximum underestimates the true maximum.
--
--   **Formalization Note.** Independence of $Z$ and $Z'$ is the paper's own modelling assumption on p. 508 ("we shall assume that $Z$ and $Z'$ are independent, with distribution given by (9)") and is a hypothesis here. Integrability of $Z\wedge Z'$ is part of the conclusion.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), p. 508, Section 3, unnumbered display before Eq. (11)

import Mathlib
import Definitions.Def_RogersSatchell_Correction_OvershootLaw

open MeasureTheory ProbabilityTheory

namespace RogersSatchell.Correction

/-- §3, p. 508, display before (11): if `Z, Z'` are independent, each with the overshoot law (9)
(`σ, h > 0`), then `Z ∧ Z'` is integrable and `E(Z ∧ Z') = √(2πh) (√2 − 1) σ / 6`. -/
theorem mean_min_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (Z Z' : Ω → ℝ)
    (hZ : HasOvershootLaw P σ h Z) (hZ' : HasOvershootLaw P σ h Z') (hind : IndepFun Z Z' P) :
    Integrable (fun ω => min (Z ω) (Z' ω)) P ∧
      ∫ ω, min (Z ω) (Z' ω) ∂P = Real.sqrt (2 * Real.pi * h) * (Real.sqrt 2 - 1) * σ / 6 := by sorry

end RogersSatchell.Correction
