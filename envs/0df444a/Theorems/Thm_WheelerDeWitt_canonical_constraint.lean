-- Prove2me | Theorems.Thm_WheelerDeWitt_canonical_constraint
-- name    : WheelerDeWitt.canonical_constraint
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-04T22:35:12.087091+00:00
-- url     : https://prove2.me/theorems/c4e8135a-7b9b-40a1-8408-5dadbec346d1
-- title:
--   Full canonical Wheeler–DeWitt action identity
-- statement:
--   For arbitrary nonempty configuration and spatial types, supplied positive-definite metric and curvature data, complex-linear derivative and matter interfaces, positive gravitational coupling and Planck constant, arbitrary cosmological constant, and every wavefunctional, configuration and point, substituting −iℏD into the coefficient-left canonical Hamiltonian yields exactly the expanded Wheeler–DeWitt expression. This is the formal algebraic derivation of equation (7), not an analytic operator construction.
-- source:
--   Claus Kiefer, Quantum Geometrodynamics: whence, whither?, Gen. Relativ. Gravit. 41 (2009), 877–901, https://arxiv.org/abs/0812.0295, Sections 2.2 and 2.4, equations (3)–(8). Formal algebraic derivation with supplied geometry and complex-linear derivative interface; no analytic realization asserted.

import Definitions.Def_wdw_canonical_operators
set_option autoImplicit false

namespace WheelerDeWitt

theorem canonical_constraint {C X : Type*} [Nonempty C] [Nonempty X]
    (g : Geometry C X) (D : FunctionalDerivative C X)
    (rho : X → Module.End ℂ (Wavefunction C))
    (kappa hbar cosmologicalConstant : ℝ) (hkappa : 0 < kappa) (hhbar : 0 < hbar)
    (psi : Wavefunction C) (q : C) (x : X) :
    quantizedHamiltonian g D rho kappa hbar cosmologicalConstant psi q x =
      wheelerDeWittExpression g D rho kappa hbar cosmologicalConstant psi q x := by
  sorry

end WheelerDeWitt
