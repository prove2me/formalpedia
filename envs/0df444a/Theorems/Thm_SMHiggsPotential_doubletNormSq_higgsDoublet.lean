-- Prove2me | Theorems.Thm_SMHiggsPotential_doubletNormSq_higgsDoublet
-- name    : SMHiggsPotential.doubletNormSq_higgsDoublet
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T23:45:45.299085+00:00
-- url     : https://prove2.me/theorems/3ae0d67c-2dd8-422d-a1fa-64e13ebc1f4d
-- title:
--   The $\beta_h$ bracket is $\Phi^\dagger\Phi$
-- statement:
--   For all real $g,M,H,\phi^0$ and complex $\phi^+$, the Higgs doublet $\Phi=(\phi^+,(v+H+i\phi^0)/\sqrt2)$, $v=2M/g$, satisfies
--   $$\Phi^\dagger\Phi=\frac{2M^2}{g^2}+\frac{2M}{g}H+\frac12\big(H^2+(\phi^0)^2+2\phi^+\phi^-\big),$$
--   which is the bracket multiplying $-\beta_h$ in box 2. (No hypothesis on $g$ is needed: for $g=0$ both sides use the Lean convention $x/0=0$.)
-- source:
--   Standard Model Lagrangian in Veltman's conventions (Feynman-'t Hooft gauge), as printed in the five-box chart supplied by the proposer (after M. Veltman, *Diagrammatica: The Path to Feynman Diagrams*, Cambridge University Press, 1994). Box 2, the non-derivative scalar terms: $-\frac12 m_h^2H^2$, the $\beta_h[\dots]$ term, $+\frac{2M^4}{g^2}\alpha_h$, $-g\alpha[H^3+H\phi^0\phi^0+2H\phi^+\phi^-]$ and $-\frac18g^2\alpha_h[H^4+\dots]$.

import Mathlib
import Definitions.Def_SMHiggsPotential_Defs
open Complex

namespace SMHiggsPotential

theorem doubletNormSq_higgsDoublet (g M H φ0 : ℝ) (φp : ℂ) :
    doubletNormSq (higgsDoublet g M H φ0 φp) =
      2 * M ^ 2 / g ^ 2 + 2 * M / g * H + (1 / 2) * (H ^ 2 + φ0 ^ 2 + 2 * normSq φp) := by sorry

end SMHiggsPotential
