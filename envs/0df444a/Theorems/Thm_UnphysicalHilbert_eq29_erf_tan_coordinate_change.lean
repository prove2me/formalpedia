-- Prove2me | Theorems.Thm_UnphysicalHilbert_eq29_erf_tan_coordinate_change
-- name    : UnphysicalHilbert.eq29_erf_tan_coordinate_change
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:08:54.555955+00:00
-- url     : https://prove2.me/theorems/a9cbd283-b188-47ff-ad9f-e46e02881d67
-- title:
--   Eq. (29) — $y=\tan(\tfrac\pi2\operatorname{erf}x)$ maps the Gaussian state to the Lorentzian state
-- statement:
--   Let $\psi(x)=\sqrt{e^{-x^2}/\sqrt\pi}$, $\phi(y)=1/\sqrt{\pi(y^2+1)}$ and
--   $$y(x)=\tan\Bigl(\frac\pi2\operatorname{erf}(x)\Bigr),\qquad \operatorname{erf}(x)=\frac2{\sqrt\pi}\int_0^xe^{-t^2}\,dt .$$
--   Then:
--
--   1. $y:\mathbb R\to\mathbb R$ is a bijection, $y$ and $y^{-1}$ are $C^\infty$, and $y$ is strictly increasing;
--   2. for every $x\in\mathbb R$,
--   $$\int_0^{y(x)}\phi(t)^2\,dt=\int_0^{x}\psi(t)^2\,dt .$$
--
--   Item 2 is the paper's eq. (26): under the change of coordinates $x\mapsto y(x)$, the Gaussian state $\psi$ becomes the state $\phi$.
--
--   **Formalization Note** Integrals are oriented interval integrals, so item 2 also covers $x<0$.
-- source:
--   G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*, arXiv:2308.06669v3 [quant-ph], 22 Dec 2024, https://arxiv.org/abs/2308.06669, Section VI, pp. 11–12, eqs. (26)–(29)

import Definitions.Def_UnphysicalHilbert_Position

namespace UnphysicalHilbert

/-- Equation (29): `y(x) = tan((π/2) erf x)` is an orientation-preserving diffeomorphism of
`ℝ` that transports the Gaussian state (27) to the Lorentzian state (28), in the sense of
eq. (26): `∫₀^{y(x)} ϕ² = ∫₀ˣ ψ²` for every `x`. -/
theorem eq29_erf_tan_coordinate_change :
    ∃ f : ℝ ≃ ℝ, (f : ℝ → ℝ) = erfTanCoordinate ∧ IsOrientationPreservingDiffeo f ∧
      ∀ x : ℝ, ∫ t in (0 : ℝ)..erfTanCoordinate x, lorentzianWave t ^ 2 =
        ∫ t in (0 : ℝ)..x, gaussianWave t ^ 2 := by
  sorry

end UnphysicalHilbert
