-- Prove2me | Theorems.Thm_WheelerDeWittSuperspace_invSuperMap_superMap
-- name    : WheelerDeWittSuperspace.invSuperMap_superMap
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T21:51:47.295719+00:00
-- url     : https://prove2.me/theorems/44503ea3-545e-4293-8978-e0d3d1e40ea5
-- title:
--   Inverse DeWitt supermetric on symmetric tensors
-- statement:
--   For positive-definite $h$ and every symmetric $p$, lowering the indices of $p$ with $G_{abcd}$ and raising them again with
--   $$G^{abcd}=\tfrac12\sqrt{\det h}\,\big(h^{ac}h^{bd}+h^{ad}h^{bc}-2h^{ab}h^{cd}\big)$$
--   returns $p$. (On antisymmetric matrices $G_{abcd}$ vanishes, so symmetry is necessary.)
-- source:
--   B. S. DeWitt, Quantum Theory of Gravity I. The Canonical Theory, Phys. Rev. 160 (1967) 1113-1148, https://doi.org/10.1103/PhysRev.160.1113; C. Kiefer, Quantum Geometrodynamics: whence, whither?, Gen. Relativ. Gravit. 41 (2009) 877-901, https://arxiv.org/abs/0812.0295, eqs. (3)-(5)

import Definitions.Def_WheelerDeWittSuperspace

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

/-- Milestone 2: `G^abcd` inverts `G_abcd` on symmetric tensors. -/
theorem invSuperMap_superMap (m p : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.PosDef) (hp : pᵀ = p) :
    invSuperMap m (superMap m p) = p := by sorry

end WheelerDeWittSuperspace
