-- Prove2me | Theorems.Thm_VolunteerEngage_Thresholds_lemma_2_i
-- name    : VolunteerEngage.Thresholds.lemma_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:39:55.325981+00:00
-- url     : https://prove2.me/theorems/5633d431-bd10-4f84-af95-ffb734c6a86c
-- title:
--   Lemma 2(i), (D1), Online Supplement p. 9 — ∫_τ^x exp{(2θz − κz²)/σ²} dz in terms of the normal cdf Φ
-- statement:
--   Let $\kappa>0$ and $\sigma>0$, and let $\theta,\tau,x$ be real numbers. Write $\Phi$ for the standard normal cumulative distribution function. Then
--   $$\int_\tau^x\exp\Big\{\frac{2\theta z-\kappa z^2}{\sigma^2}\Big\}\,dz=\frac{\sigma\sqrt\pi}{\sqrt\kappa}\exp\Big\{\frac{\theta^2}{\kappa\sigma^2}\Big\}\Big[\Phi\Big(\frac{x-\theta/\kappa}{\sigma/\sqrt{2\kappa}}\Big)-\Phi\Big(\frac{\tau-\theta/\kappa}{\sigma/\sqrt{2\kappa}}\Big)\Big].$$
--
--   This evaluates the integral of the integrating factor of the linear equation that the Bellman equation becomes on a threshold interval; it is the source of the $\Phi$ terms in the closed form $u_l$.
--
--   **Formalization Note** The integral is the oriented interval integral, so the identity is stated for all real $\tau$ and $x$ (for $x<\tau$ both sides change sign). The positivity of $\kappa$ and $\sigma$ is the paper's standing assumption, stated explicitly. $\Phi$ is `Cohen2019.Robust.Phi` $=$ `cdf (gaussianReal 0 1)`.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 9, Lemma 2(i), (D1)

import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi

namespace VolunteerEngage.Thresholds

/-- Lemma 2(i), (D1), Online Supplement p. 9: for `κ > 0`, `σ > 0` and all real `θ`, `τ`, `x`,
`∫_τ^x exp{(2θz - κz²)/σ²} dz = (σ√π/√κ) exp{θ²/(κσ²)}
  [Φ((x - θ/κ)/(σ/√(2κ))) - Φ((τ - θ/κ)/(σ/√(2κ)))]`,
with `Φ` the standard normal cumulative distribution function and the integral oriented. -/
theorem lemma_2_i (κ σ θ τ x : ℝ) (hκ : 0 < κ) (hσ : 0 < σ) :
    ∫ z in τ..x, Real.exp ((2 * θ * z - κ * z ^ 2) / σ ^ 2) =
      σ * Real.sqrt Real.pi / Real.sqrt κ * Real.exp (θ ^ 2 / (κ * σ ^ 2)) *
        (Cohen2019.Robust.Phi ((x - θ / κ) / (σ / Real.sqrt (2 * κ)))
          - Cohen2019.Robust.Phi ((τ - θ / κ) / (σ / Real.sqrt (2 * κ)))) := by sorry

end VolunteerEngage.Thresholds
