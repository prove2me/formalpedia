-- Prove2me | Theorems.Thm_SMHiggsPotential_quartic_bracket_eq_sq
-- name    : SMHiggsPotential.quartic_bracket_eq_sq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T23:47:45.917893+00:00
-- url     : https://prove2.me/theorems/fdf8b1d6-4e30-4741-a25e-d1641ef0ce84
-- title:
--   The quartic bracket is $(H^2+\phi^0\phi^0+2\phi^+\phi^-)^2$
-- statement:
--   For all real $H,\phi^0,p$ (with $p=\phi^+\phi^-$ in the application),
--   $$H^4+(\phi^0)^4+4p^2+4(\phi^0)^2p+4H^2p+2(\phi^0)^2H^2=(H^2+(\phi^0)^2+2p)^2.$$
--   This is the bracket of the quartic term of box 2.
-- source:
--   Standard Model Lagrangian in Veltman's conventions (Feynman-'t Hooft gauge), as printed in the five-box chart supplied by the proposer (after M. Veltman, *Diagrammatica: The Path to Feynman Diagrams*, Cambridge University Press, 1994). Box 2, the non-derivative scalar terms: $-\frac12 m_h^2H^2$, the $\beta_h[\dots]$ term, $+\frac{2M^4}{g^2}\alpha_h$, $-g\alpha[H^3+H\phi^0\phi^0+2H\phi^+\phi^-]$ and $-\frac18g^2\alpha_h[H^4+\dots]$.

import Mathlib
import Definitions.Def_SMHiggsPotential_Defs
open Complex

namespace SMHiggsPotential

theorem quartic_bracket_eq_sq (H φ0 p : ℝ) :
    H ^ 4 + φ0 ^ 4 + 4 * p ^ 2 + 4 * φ0 ^ 2 * p + 4 * H ^ 2 * p + 2 * φ0 ^ 2 * H ^ 2 =
      (H ^ 2 + φ0 ^ 2 + 2 * p) ^ 2 := by sorry

end SMHiggsPotential
