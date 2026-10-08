-- Prove2me | Theorems.Thm_SMHiggsPotential_scalarLagrangian_unitary_invariant
-- name    : SMHiggsPotential.scalarLagrangian_unitary_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T23:48:43.236713+00:00
-- url     : https://prove2.me/theorems/3de1c97c-3102-4865-840a-9c4337743397
-- title:
--   The box 2 scalar terms are $U(2)$-invariant
-- statement:
--   Let $g\neq0$, $M\neq0$ and $m_h,\beta_h\in\mathbb R$. Let $(H,\phi^0,\phi^+)$ and $(H',\phi^{0\prime},\phi^{+\prime})$ be two field configurations, and let $U$ be a $2\times2$ unitary matrix with $\Phi(H',\phi^{0\prime},\phi^{+\prime})=U\,\Phi(H,\phi^0,\phi^+)$. Then the scalar terms of box 2 agree:
--   $$\mathcal L_V(H',\phi^{0\prime},\phi^{+\prime})=\mathcal L_V(H,\phi^0,\phi^+).$$
-- source:
--   Standard Model Lagrangian in Veltman's conventions (Feynman-'t Hooft gauge), as printed in the five-box chart supplied by the proposer (after M. Veltman, *Diagrammatica: The Path to Feynman Diagrams*, Cambridge University Press, 1994). Box 2, the non-derivative scalar terms: $-\frac12 m_h^2H^2$, the $\beta_h[\dots]$ term, $+\frac{2M^4}{g^2}\alpha_h$, $-g\alpha[H^3+H\phi^0\phi^0+2H\phi^+\phi^-]$ and $-\frac18g^2\alpha_h[H^4+\dots]$.

import Mathlib
import Definitions.Def_SMHiggsPotential_Defs
open Complex

namespace SMHiggsPotential

theorem scalarLagrangian_unitary_invariant (g M mh βh H φ0 H' φ0' : ℝ) (φp φp' : ℂ)
    (hM : M ≠ 0) (hg : g ≠ 0) (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (hU : higgsDoublet g M H' φ0' φp' =
      Matrix.mulVec (U : Matrix (Fin 2) (Fin 2) ℂ) (higgsDoublet g M H φ0 φp)) :
    scalarLagrangian g M mh βh H' φ0' φp' = scalarLagrangian g M mh βh H φ0 φp := by sorry

end SMHiggsPotential
