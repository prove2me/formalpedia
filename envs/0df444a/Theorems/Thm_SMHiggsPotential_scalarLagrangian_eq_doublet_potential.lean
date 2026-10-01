-- Prove2me | Theorems.Thm_SMHiggsPotential_scalarLagrangian_eq_doublet_potential
-- name    : SMHiggsPotential.scalarLagrangian_eq_doublet_potential
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T23:41:54.925888+00:00
-- url     : https://prove2.me/theorems/70c1b0ae-580e-4466-8607-10ad33d1365d
-- title:
--   Box 2 scalar terms $=-\lambda(\Phi^\dagger\Phi)^2+(\tfrac12m_h^2-\beta_h)\,\Phi^\dagger\Phi$
-- statement:
--   Let $g\neq0$ and $M\neq0$, and let $m_h,\beta_h$ be real. For all real $H,\phi^0$ and complex $\phi^+$, the non-derivative scalar terms $\mathcal L_V$ of box 2 (see the definition file) depend on the fields only through the doublet norm $\Phi^\dagger\Phi$, with $\Phi=(\phi^+,(v+H+i\phi^0)/\sqrt2)$ and $v=2M/g$:
--   $$\mathcal L_V=-\lambda\,(\Phi^\dagger\Phi)^2+\Big(\frac{m_h^2}{2}-\beta_h\Big)\Phi^\dagger\Phi,\qquad \lambda=\frac{g^2m_h^2}{8M^2}.$$
--   So the scalar sector of the chart is minus the standard Higgs potential $V(\Phi)=\lambda(\Phi^\dagger\Phi)^2-\mu^2\Phi^\dagger\Phi$ with $\mu^2=\frac{m_h^2}{2}-\beta_h$. Equivalently, $\mathcal L_V=-\lambda(\Phi^\dagger\Phi-\frac{v^2}{2})^2-\beta_h\Phi^\dagger\Phi+\frac{2M^4}{g^2}\alpha_h$.
-- source:
--   Standard Model Lagrangian in Veltman's conventions (Feynman-'t Hooft gauge), as printed in the five-box chart supplied by the proposer (after M. Veltman, *Diagrammatica: The Path to Feynman Diagrams*, Cambridge University Press, 1994). Box 2, the non-derivative scalar terms: $-\frac12 m_h^2H^2$, the $\beta_h[\dots]$ term, $+\frac{2M^4}{g^2}\alpha_h$, $-g\alpha[H^3+H\phi^0\phi^0+2H\phi^+\phi^-]$ and $-\frac18g^2\alpha_h[H^4+\dots]$.

import Mathlib
import Definitions.Def_SMHiggsPotential_Defs
open Complex

namespace SMHiggsPotential

theorem scalarLagrangian_eq_doublet_potential (g M mh βh H φ0 : ℝ) (φp : ℂ)
    (hM : M ≠ 0) (hg : g ≠ 0) :
    scalarLagrangian g M mh βh H φ0 φp =
      - quarticCoupling g M mh * doubletNormSq (higgsDoublet g M H φ0 φp) ^ 2
        + (mh ^ 2 / 2 - βh) * doubletNormSq (higgsDoublet g M H φ0 φp) := by sorry

end SMHiggsPotential
