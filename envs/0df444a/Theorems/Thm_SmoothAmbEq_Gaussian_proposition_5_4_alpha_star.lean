-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_proposition_5_4_alpha_star
-- name    : SmoothAmbEq.Gaussian.proposition_5_4_alpha_star
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:13.013392+00:00
-- url     : https://prove2.me/theorems/199d3a40-f807-4414-a17c-e2617a83656b
-- title:
--   Proposition 5.4, p. 17 — there is a unique α* < 0 solving (5.17)
-- statement:
--   There exists a unique $\alpha^*<0$ such that
--   $$\Big(1+\sigma_0^{-2}\sigma^2T^{-1}\Big)\int_0^\infty e^{-x}\big(1+(1-\alpha^*)x\big)^{\frac{\alpha^*}{1-\alpha^*}}dx=1.\qquad(5.17)$$
--
--   $\alpha^*$ is the critical degree of ambiguity seeking: Theorem 5.5 and the solvability of (5.16) hold for $\alpha>\alpha^*$.
--
--   **Formalization Note** The integral is a Lebesgue integral over $(0,\infty)$; for $\alpha^*<0$ the integrand lies in $(0,e^{-x}]$.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 17, Proposition 5.4, (5.17)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory Set

namespace SmoothAmbEq.Gaussian

/-- Proposition 5.4, p. 17 (first sentence): there exists a unique `α* < 0` such that
(5.17) `(1 + σ₀⁻²σ²T⁻¹) ∫₀^∞ e^{-x}(1 + (1 - α*)x)^{α*/(1-α*)} dx = 1`. -/
theorem proposition_5_4_alpha_star (M : Model) : ∃! a : ℝ, IsAlphaStar M a := by sorry

end SmoothAmbEq.Gaussian
