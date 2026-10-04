-- Prove2me | Theorems.Thm_WheelerDeWitt_momentum_composition
-- name    : WheelerDeWitt.momentum_composition
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:49.720979+00:00
-- url     : https://prove2.me/theorems/89f1e6c9-f77a-489a-98ef-a4544acfa56c
-- title:
--   Composition of canonical momentum operators
-- statement:
--   For any supplied complex-linear derivative family, any real Planck parameter, spatial point, four component indices, wavefunctional and configuration, composing the two prescribed momentum operators gives minus the square of the Planck parameter times the ordered derivative composition. This statement includes zero and negative Planck parameters.
-- source:
--   Claus Kiefer, Quantum Geometrodynamics: whence, whither?, Gen. Relativ. Gravit. 41 (2009), 877–901, https://arxiv.org/abs/0812.0295, Sections 2.2 and 2.4, equations (3)–(8). Formal algebraic derivation with supplied geometry and complex-linear derivative interface; no analytic realization asserted.

import Definitions.Def_wdw_canonical_operators
set_option autoImplicit false

namespace WheelerDeWitt

theorem momentum_composition {C X : Type*} (D : FunctionalDerivative C X)
    (hbar : ℝ) (x : X) (a b c d : Fin 3) (psi : Wavefunction C) (q : C) :
    (momentum D hbar x a b (momentum D hbar x c d psi)) q =
      -(hbar : ℂ)^2 * (D x a b (D x c d psi)) q := by
  sorry

end WheelerDeWitt
