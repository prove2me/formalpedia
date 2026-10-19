-- Prove2me | Theorems.Thm_Penrose_delta_double_integral
-- name    : Penrose.delta_double_integral
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T18:22:21.259662+00:00
-- url     : https://prove2.me/theorems/fac2fde9-aea8-46f8-966c-8f19f7fab51c
-- title:
--   The measure as the self-energy double integral of the difference
-- statement:
--   For two smooth, rapidly decreasing mass densities $\rho, \rho'$ on $\mathbb{R}^3$ and any real $G$, Penrose's measure of incompatibility satisfies
--
--   $$\Delta(\rho,\rho') = 4\pi G^2 \iint_{\mathbb{R}^3\times\mathbb{R}^3} \frac{(\rho-\rho')(x)\,(\rho-\rho')(y)}{\|x-y\|}\,dx\,dy.$$
--
--   This is the final displayed formula of the chain in Section 6 of Penrose (1996, p. 595): substituting the integral formula for the potential into the pairing expresses $\Delta$ as $4\pi G^2$ times the double integral of the difference distribution against itself over the Newtonian kernel. The paper displays this formula with coefficient $-4\pi G$; under the sign convention that makes the first three steps of its chain verbatim, the correct coefficient is $+4\pi G^2$ — a sign and constant slip in the paper's display, documented in the mission description.
--
--   Up to the explicit constant, the right-hand side is the gravitational self-energy of the difference distribution — the content of the mission's goal theorem.
-- source:
--   Penrose 1996, On Gravity's Role in Quantum State Reduction, General Relativity and Gravitation 28(5):581-600, https://doi.org/10.1007/BF02105068, Section 6, p. 595, final displayed formula Δ = -4πG∬(ρ-ρ')(ρ-ρ')/|x-y|d³xd³y (sign and constant corrected under the mission's convention; see mission description)

import Mathlib
import Definitions.Def_penrose

open MeasureTheory

namespace Penrose

theorem delta_double_integral (G : ℝ) (ρ ρ' : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ) :
    deltaMeasure G ρ ρ'
      = 4 * Real.pi * G ^ 2
        * ∫ x, ∫ y, (⇑ρ x - ⇑ρ' x) * (⇑ρ y - ⇑ρ' y) / ‖x - y‖ ∂volume ∂volume := by sorry

end Penrose
