-- Prove2me | Theorems.Thm_WheelerDeWitt_constraint_iff
-- name    : WheelerDeWitt.constraint_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-04T22:22:22.842226+00:00
-- url     : https://prove2.me/theorems/2bece37e-a25b-465c-9d3b-07a5419bc496
-- title:
--   Equivalence of the canonical and expanded zero constraints
-- statement:
--   For arbitrary nonempty configuration and spatial types and the supplied metric, curvature, derivative and matter interfaces, with positive gravitational coupling and Planck constant, the quantized Hamiltonian vanishes at every configuration and spatial point if and only if its expanded Wheeler–DeWitt expression does. It does not assert that a nonzero solution exists.
-- source:
--   Claus Kiefer, Quantum Geometrodynamics: whence, whither?, Gen. Relativ. Gravit. 41 (2009), 877–901, https://arxiv.org/abs/0812.0295, Sections 2.2 and 2.4, equations (3)–(8). Formal algebraic derivation with supplied geometry and complex-linear derivative interface; no analytic realization asserted.

import Definitions.Def_wdw_canonical_operators
set_option autoImplicit false

namespace WheelerDeWitt

theorem constraint_iff {C X : Type*} [Nonempty C] [Nonempty X]
    (g : Geometry C X) (D : FunctionalDerivative C X)
    (rho : X → Module.End ℂ (Wavefunction C))
    (kappa hbar cosmologicalConstant : ℝ) (hkappa : 0 < kappa) (hhbar : 0 < hbar)
    (psi : Wavefunction C) :
    (∀ q x, quantizedHamiltonian g D rho kappa hbar cosmologicalConstant psi q x = 0) ↔
    (∀ q x, wheelerDeWittExpression g D rho kappa hbar cosmologicalConstant psi q x = 0) := by
  sorry

end WheelerDeWitt
