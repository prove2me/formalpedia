-- Prove2me | Theorems.Thm_VolunteerEngage_Thresholds_lemma_2_ii
-- name    : VolunteerEngage.Thresholds.lemma_2_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:00.656561+00:00
-- url     : https://prove2.me/theorems/39b4909c-8aae-47cb-b1a8-4d9a3877fad7
-- title:
--   Lemma 2(ii), (D2), Online Supplement p. 9 — ∫_τ^x z·exp{(2θz − κz²)/σ²} dz in terms of Φ and exp
-- statement:
--   Let $\kappa>0$ and $\sigma>0$, and let $\theta,\tau,x$ be real numbers. Write $\Phi$ for the standard normal cumulative distribution function. Then
--   $$\int_\tau^x z\exp\Big\{\frac{2\theta z-\kappa z^2}{\sigma^2}\Big\}\,dz=\frac{\theta\sigma\sqrt\pi}{\kappa\sqrt\kappa}\exp\Big\{\frac{\theta^2}{\kappa\sigma^2}\Big\}\Big[\Phi\Big(\frac{x-\theta/\kappa}{\sigma/\sqrt{2\kappa}}\Big)-\Phi\Big(\frac{\tau-\theta/\kappa}{\sigma/\sqrt{2\kappa}}\Big)\Big]+\frac{\sigma^2}{2\kappa}\Big[\exp\Big\{\frac{2\theta\tau-\kappa\tau^2}{\sigma^2}\Big\}-\exp\Big\{\frac{2\theta x-\kappa x^2}{\sigma^2}\Big\}\Big].$$
--
--   Together with Lemma 2(i), this evaluates the integrals that arise when the linear equation on a threshold interval is solved with its integrating factor.
--
--   **Formalization Note** The integral is the oriented interval integral, so the identity is stated for all real $\tau$ and $x$. The positivity of $\kappa$ and $\sigma$ is the paper's standing assumption, stated explicitly. $\Phi$ is `Cohen2019.Robust.Phi` $=$ `cdf (gaussianReal 0 1)`.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 9, Lemma 2(ii), (D2)

import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi

namespace VolunteerEngage.Thresholds

/-- Lemma 2(ii), (D2), Online Supplement p. 9: for `κ > 0`, `σ > 0` and all real `θ`, `τ`, `x`,
`∫_τ^x z exp{(2θz - κz²)/σ²} dz = (θσ√π/(κ√κ)) exp{θ²/(κσ²)}
  [Φ((x - θ/κ)/(σ/√(2κ))) - Φ((τ - θ/κ)/(σ/√(2κ)))]
  + (σ²/(2κ)) [exp{(2θτ - κτ²)/σ²} - exp{(2θx - κx²)/σ²}]`,
with `Φ` the standard normal cumulative distribution function and the integral oriented. -/
theorem lemma_2_ii (κ σ θ τ x : ℝ) (hκ : 0 < κ) (hσ : 0 < σ) :
    ∫ z in τ..x, z * Real.exp ((2 * θ * z - κ * z ^ 2) / σ ^ 2) =
      θ * σ * Real.sqrt Real.pi / (κ * Real.sqrt κ) * Real.exp (θ ^ 2 / (κ * σ ^ 2)) *
        (Cohen2019.Robust.Phi ((x - θ / κ) / (σ / Real.sqrt (2 * κ)))
          - Cohen2019.Robust.Phi ((τ - θ / κ) / (σ / Real.sqrt (2 * κ))))
      + σ ^ 2 / (2 * κ) *
        (Real.exp ((2 * θ * τ - κ * τ ^ 2) / σ ^ 2) - Real.exp ((2 * θ * x - κ * x ^ 2) / σ ^ 2)) := by sorry

end VolunteerEngage.Thresholds
