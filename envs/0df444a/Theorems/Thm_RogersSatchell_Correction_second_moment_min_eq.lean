-- Prove2me | Theorems.Thm_RogersSatchell_Correction_second_moment_min_eq
-- name    : RogersSatchell.Correction.second_moment_min_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:41.613907+00:00
-- url     : https://prove2.me/theorems/bbb5267f-b09d-4f62-9251-54f4937bd3f4
-- title:
--   Eq. (13) — for independent Z, Z′ with law (9), E[(Z ∧ Z′)²] = (σ²h/4)(1 − π/4)
-- statement:
--   Let $\sigma > 0$ and $h > 0$, and let $Z$ and $Z'$ be independent random variables on a probability space, each with distribution (9): $P(Z>\alpha) = P(Z'>\alpha) = G_{\sigma,h}(\alpha)$ for every $\alpha \ge 0$. Then $Z\wedge Z'$ is square integrable and
--
--   $$E\big[(Z\wedge Z')^2\big] \;=\; \frac{\sigma^2 h}{4}\Big(1 - \frac{\pi}{4}\Big) .$$
--
--   With (12) this gives the second moment of $Z\vee Z'$ on p. 509.
--
--   **Formalization Note.** The paper writes $E(Z\wedge Z')^2$, meaning the expectation of the square, as its first line (an integral against $2\alpha\,d\alpha$) shows. Independence is the paper's modelling assumption of p. 508. Square integrability is part of the conclusion.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), p. 509, Section 3, Eq. (13)

import Mathlib
import Definitions.Def_RogersSatchell_Correction_OvershootLaw

open MeasureTheory ProbabilityTheory

namespace RogersSatchell.Correction

/-- (13), §3, p. 509: if `Z, Z'` are independent, each with the overshoot law (9) (`σ, h > 0`),
then `Z ∧ Z' ∈ L²` and `E[(Z ∧ Z')²] = (σ² h / 4)(1 − π/4)`. -/
theorem second_moment_min_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (Z Z' : Ω → ℝ)
    (hZ : HasOvershootLaw P σ h Z) (hZ' : HasOvershootLaw P σ h Z') (hind : IndepFun Z Z' P) :
    MemLp (fun ω => min (Z ω) (Z' ω)) 2 P ∧
      ∫ ω, min (Z ω) (Z' ω) ^ 2 ∂P = σ ^ 2 * h / 4 * (1 - Real.pi / 4) := by sorry

end RogersSatchell.Correction
