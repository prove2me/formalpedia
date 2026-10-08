-- Prove2me | Theorems.Thm_WheelerDeWittSuperspace_superQuad_pos_of_traceless
-- name    : WheelerDeWittSuperspace.superQuad_pos_of_traceless
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T21:25:08.481396+00:00
-- url     : https://prove2.me/theorems/4578b020-0863-479f-a9f0-fba2b7e06bd5
-- title:
--   DeWitt supermetric is positive on traceless momenta
-- statement:
--   Let $h$ be a positive-definite $3\times3$ matrix and $p\neq0$ a symmetric matrix with $\operatorname{tr}(hp)=0$. Then
--   $$G_{abcd}(h)\,p^{ab}p^{cd}>0,\qquad G_{abcd}=\frac{h_{ac}h_{bd}+h_{ad}h_{bc}-h_{ab}h_{cd}}{2\sqrt{\det h}}.$$
--   This is the positive five-dimensional part of the Lorentzian signature of the supermetric.
-- source:
--   B. S. DeWitt, Quantum Theory of Gravity I. The Canonical Theory, Phys. Rev. 160 (1967) 1113-1148, https://doi.org/10.1103/PhysRev.160.1113, Section 5; C. Kiefer, Quantum Geometrodynamics: whence, whither?, Gen. Relativ. Gravit. 41 (2009) 877-901, https://arxiv.org/abs/0812.0295, eq. (5)

import Definitions.Def_WheelerDeWittSuperspace

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

/-- Milestone 1 (Lorentzian signature, positive part): the supermetric is positive on
nonzero symmetric momenta that are traceless with respect to `h`. -/
theorem superQuad_pos_of_traceless (m p : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.PosDef)
    (hp : pᵀ = p) (hp0 : p ≠ 0) (htr : (m * p).trace = 0) :
    0 < superQuad m p := by sorry

end WheelerDeWittSuperspace
