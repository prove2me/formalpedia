-- Prove2me | Theorems.Thm_WheelerDeWitt_volumeDensity_pos
-- name    : WheelerDeWitt.volumeDensity_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:09:27.24965+00:00
-- url     : https://prove2.me/theorems/9c28a5aa-e884-40fc-8f7e-8bd69f189a5c
-- title:
--   Positive spatial metric volume density
-- statement:
--   For every supplied spatial geometry, configuration and spatial point, the square root of the positive metric determinant is strictly positive.
-- source:
--   Claus Kiefer, Quantum Geometrodynamics: whence, whither?, Gen. Relativ. Gravit. 41 (2009), 877–901, https://arxiv.org/abs/0812.0295, Sections 2.2 and 2.4, equations (3)–(8). Formal algebraic derivation with supplied geometry and complex-linear derivative interface; no analytic realization asserted.

import Definitions.Def_wdw_canonical_operators
set_option autoImplicit false

namespace WheelerDeWitt

theorem volumeDensity_pos {C X : Type*} (g : Geometry C X) (q : C) (x : X) :
    0 < volumeDensity g q x := by
  sorry

end WheelerDeWitt
