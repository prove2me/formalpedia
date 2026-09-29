-- Prove2me | Theorems.Thm_RaritaSchwinger_massive_equation_implies_constraints_and_dirac
-- name    : RaritaSchwinger.massive_equation_implies_constraints_and_dirac
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T11:40:42.65527+00:00
-- url     : https://prove2.me/theorems/b677aeac-cd37-4a01-b93a-abe0fe77cb2e
-- title:
--   Free massive Rarita–Schwinger field: $\gamma^\mu\psi_\mu=0$, $\partial^\mu\psi_\mu=0$ and $(\gamma^\nu\partial_\nu-im)\psi_\mu=0$
-- statement:
--   Let $\gamma^\mu$ be gamma matrices for $\eta=\mathrm{diag}(1,-1,-1,-1)$, let $m>0$, and let $\psi_\mu$ be a vector-spinor field on $\mathbb R^4$ of class $C^2$ solving the massive free Rarita–Schwinger equation
--   $$\bigl(\epsilon^{\mu\kappa\rho\nu}\gamma_5\gamma_\kappa\partial_\rho-im\sigma^{\mu\nu}\bigr)\psi_\nu=0,\qquad\epsilon^{0123}=+1,\ \gamma_5=i\gamma_0\gamma_1\gamma_2\gamma_3,\ \sigma^{\mu\nu}=\tfrac i2[\gamma^\mu,\gamma^\nu].$$
--   Then at every point $x$:
--   1. $\gamma^\mu\psi_\mu(x)=0$;
--   2. $\partial^\mu\psi_\mu(x)=0$;
--   3. every vector component obeys the Dirac equation
--   $$\gamma^\nu\partial_\nu\psi_\mu(x)-im\,\psi_\mu(x)=0\qquad(\mu=0,1,2,3).$$
--
--   The source writes the Dirac equation as $(\gamma^\nu\partial_\nu+m)\psi_\mu=0$ "up to convention-dependent factors of $i$"; with the conventions fixed here ($\eta$ mostly minus, $\epsilon^{0123}=+1$, $\gamma_5$ built from lowered gamma matrices) the factor in front of $m$ is $-i$.
--
--   **Formalization Note** $C^2$ regularity is assumed so that the equation can be differentiated and second derivatives commute; the result is stated for every gamma family, not a particular representation.
-- source:
--   "Rarita–Schwinger equation", Wikipedia, revision oldid=1362709293, https://en.wikipedia.org/w/index.php?title=Rarita%E2%80%93Schwinger_equation&oldid=1362709293; section 'Massive field and constraints' (constraints and Dirac equation on each vector component); massive equation from the lead section.

import Definitions.Def_RaritaSchwinger_core

open DiracEquation

namespace RaritaSchwinger

theorem massive_equation_implies_constraints_and_dirac
    (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g)
    (m : ℝ) (hm : 0 < m) (psi : VectorSpinorField) (hpsi : ContDiff ℝ 2 psi)
    (hEq : IsMassiveRSSolution g m psi) :
    ∀ x, gammaTrace g psi x = 0 ∧ divergence psi x = 0 ∧
      ∀ mu, diracOperator g psi mu x - (Complex.I * (m : ℂ)) • psi x mu = 0 := by sorry

end RaritaSchwinger
