-- Prove2me | Theorems.Thm_SMHiggsPotential_scalarLagrangian_tadpole
-- name    : SMHiggsPotential.scalarLagrangian_tadpole
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T23:53:47.266839+00:00
-- url     : https://prove2.me/theorems/36ddaf2d-599b-405a-9f96-9be2641e90b5
-- title:
--   $\beta_h$ is the tadpole: $\partial_H\mathcal L_V|_{0}=-\tfrac{2M}{g}\beta_h$
-- statement:
--   For all real $g,M,m_h,\beta_h$, the function $H\mapsto\mathcal L_V(H,0,0)$ (the scalar terms of box 2 with $\phi^0=\phi^+=0$) is differentiable at $H=0$ with derivative
--   $$\frac{d}{dH}\mathcal L_V(H,0,0)\Big|_{H=0}=-\frac{2M}{g}\,\beta_h.$$
-- source:
--   Standard Model Lagrangian in Veltman's conventions (Feynman-'t Hooft gauge), as printed in the five-box chart supplied by the proposer (after M. Veltman, *Diagrammatica: The Path to Feynman Diagrams*, Cambridge University Press, 1994). Box 2, the non-derivative scalar terms: $-\frac12 m_h^2H^2$, the $\beta_h[\dots]$ term, $+\frac{2M^4}{g^2}\alpha_h$, $-g\alpha[H^3+H\phi^0\phi^0+2H\phi^+\phi^-]$ and $-\frac18g^2\alpha_h[H^4+\dots]$.

import Mathlib
import Definitions.Def_SMHiggsPotential_Defs
open Complex

namespace SMHiggsPotential

theorem scalarLagrangian_tadpole (g M mh βh : ℝ) :
    HasDerivAt (fun H : ℝ => scalarLagrangian g M mh βh H 0 0) (-(2 * M / g) * βh) 0 := by sorry

end SMHiggsPotential
