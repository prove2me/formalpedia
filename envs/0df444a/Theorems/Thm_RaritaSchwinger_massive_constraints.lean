-- Prove2me | Theorems.Thm_RaritaSchwinger_massive_constraints
-- name    : RaritaSchwinger.massive_constraints
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T11:40:02.304539+00:00
-- url     : https://prove2.me/theorems/69def83a-573d-48ad-9a70-76ceca32b51f
-- title:
--   The massive Rarita–Schwinger equation implies $\gamma^\mu\psi_\mu=0$ and $\partial^\mu\psi_\mu=0$
-- statement:
--   Let $\gamma^\mu$ be gamma matrices for $\eta=\mathrm{diag}(1,-1,-1,-1)$, let $m>0$, and let $\psi_\mu$ be a vector-spinor field on $\mathbb R^4$ of class $C^2$ solving the massive free Rarita–Schwinger equation
--   $$\bigl(\epsilon^{\mu\kappa\rho\nu}\gamma_5\gamma_\kappa\partial_\rho-im\sigma^{\mu\nu}\bigr)\psi_\nu=0,\qquad\epsilon^{0123}=+1,\ \gamma_5=i\gamma_0\gamma_1\gamma_2\gamma_3,\ \sigma^{\mu\nu}=\tfrac i2[\gamma^\mu,\gamma^\nu].$$
--   Then at every point
--   $$\gamma^\mu\psi_\mu=0,\qquad\partial^\mu\psi_\mu=0 .$$
--
--   These are the spin-$3/2$ analogue of the Fierz–Pauli subsidiary conditions: they follow from the field equation and remove the lower-spin sector.
--
--   **Formalization Note** $C^2$ regularity is assumed so that the equation can be differentiated and second derivatives commute.
-- source:
--   "Rarita–Schwinger equation", Wikipedia, revision oldid=1362709293, https://en.wikipedia.org/w/index.php?title=Rarita%E2%80%93Schwinger_equation&oldid=1362709293; section 'Massive field and constraints', constraints $\gamma^\mu\psi_\mu=0$, $\partial^\mu\psi_\mu=0$; massive equation from the lead section.

import Definitions.Def_RaritaSchwinger_core

open DiracEquation

namespace RaritaSchwinger

theorem massive_constraints (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g)
    (m : ℝ) (hm : 0 < m) (psi : VectorSpinorField) (hpsi : ContDiff ℝ 2 psi)
    (hEq : IsMassiveRSSolution g m psi) :
    ∀ x, gammaTrace g psi x = 0 ∧ divergence psi x = 0 := by sorry

end RaritaSchwinger
