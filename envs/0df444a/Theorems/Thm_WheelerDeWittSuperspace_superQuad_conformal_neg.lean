-- Prove2me | Theorems.Thm_WheelerDeWittSuperspace_superQuad_conformal_neg
-- name    : WheelerDeWittSuperspace.superQuad_conformal_neg
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T21:38:21.901979+00:00
-- url     : https://prove2.me/theorems/decdd34a-d816-40e9-80fe-4103eb61eb99
-- title:
--   The conformal direction of superspace is timelike
-- statement:
--   For every positive-definite $3\times3$ matrix $h$,
--   $$G_{abcd}(h)\,(h^{-1})^{ab}(h^{-1})^{cd}<0 .$$
--   Together with positivity on $h$-traceless symmetric momenta, the DeWitt supermetric on the six-dimensional space of symmetric momenta has signature $(5,1)$; the negative direction is the conformal (volume) mode.
-- source:
--   B. S. DeWitt, Quantum Theory of Gravity I. The Canonical Theory, Phys. Rev. 160 (1967) 1113-1148, https://doi.org/10.1103/PhysRev.160.1113, Section 5; C. Kiefer, Quantum Geometrodynamics: whence, whither?, Gen. Relativ. Gravit. 41 (2009) 877-901, https://arxiv.org/abs/0812.0295, eq. (5)

import Definitions.Def_WheelerDeWittSuperspace

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

/-- Milestone 1 (Lorentzian signature, negative direction): the conformal direction
`p = h⁻¹` is timelike. -/
theorem superQuad_conformal_neg (m : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.PosDef) :
    superQuad m m⁻¹ < 0 := by sorry

end WheelerDeWittSuperspace
