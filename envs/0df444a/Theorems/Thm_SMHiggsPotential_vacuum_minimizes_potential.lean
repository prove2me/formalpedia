-- Prove2me | Theorems.Thm_SMHiggsPotential_vacuum_minimizes_potential
-- name    : SMHiggsPotential.vacuum_minimizes_potential
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T00:08:06.364357+00:00
-- url     : https://prove2.me/theorems/e90189e7-eae8-464f-8e6e-8b8c04e152d0
-- title:
--   With $\beta_h=0$, the vacuum $H=\phi^0=\phi^\pm=0$ minimizes the potential
-- statement:
--   Let $g,M,m_h$ be real and set $\beta_h=0$. For all real $H,\phi^0$ and complex $\phi^+$,
--   $$\mathcal L_V(H,\phi^0,\phi^+)\le\mathcal L_V(0,0,0).$$
--   So the vacuum $\Phi=(0,v/\sqrt2)$ is a global minimum of the scalar potential $V=-\mathcal L_V$ of box 2. (The degenerate cases $M=0$ or $g=0$ are included; there $\mathcal L_V=-\frac12m_h^2H^2$ under the convention $x/0=0$.)
-- source:
--   Standard Model Lagrangian in Veltman's conventions (Feynman-'t Hooft gauge), as printed in the five-box chart supplied by the proposer (after M. Veltman, *Diagrammatica: The Path to Feynman Diagrams*, Cambridge University Press, 1994). Box 2, the non-derivative scalar terms: $-\frac12 m_h^2H^2$, the $\beta_h[\dots]$ term, $+\frac{2M^4}{g^2}\alpha_h$, $-g\alpha[H^3+H\phi^0\phi^0+2H\phi^+\phi^-]$ and $-\frac18g^2\alpha_h[H^4+\dots]$.

import Mathlib
import Definitions.Def_SMHiggsPotential_Defs
open Complex

namespace SMHiggsPotential

theorem vacuum_minimizes_potential (g M mh H φ0 : ℝ) (φp : ℂ) :
    scalarLagrangian g M mh 0 H φ0 φp ≤ scalarLagrangian g M mh 0 0 0 0 := by sorry

end SMHiggsPotential
