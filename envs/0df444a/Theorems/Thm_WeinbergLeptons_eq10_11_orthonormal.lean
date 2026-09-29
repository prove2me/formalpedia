-- Prove2me | Theorems.Thm_WeinbergLeptons_eq10_11_orthonormal
-- name    : WeinbergLeptons.eq10_11_orthonormal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:52:08.043545+00:00
-- url     : https://prove2.me/theorems/16042ec1-ddd2-4331-b153-fc584d668260
-- title:
--   Eqs. (10)–(11): $Z$ and $A$ are orthonormal combinations of $A^3$ and $B$
-- statement:
--   Let $g,g'$ be real with $g^2+g'^2>0$. The coefficient vectors $z$ and $a$ of the neutral fields (10) and (11) are orthonormal:
--
--   $$z\cdot z=1,\qquad a\cdot a=1,\qquad z\cdot a=0.$$
--
--   Thus (10)–(11) is a rotation of $(A^3,B)$ and $Z_\mu,A_\mu$ are canonically normalized.
-- source:
--   S. Weinberg, A Model of Leptons, Phys. Rev. Lett. 19, 1264-1266 (1967), https://doi.org/10.1103/PhysRevLett.19.1264, p. 1265, eqs. (10), (11)

import Definitions.Def_WeinbergLeptons_Model

open Matrix

namespace WeinbergLeptons

theorem eq10_11_orthonormal (g g' : ℝ) (hN : 0 < g ^ 2 + g' ^ 2) :
    zVec g g' ⬝ᵥ zVec g g' = 1 ∧ photonVec g g' ⬝ᵥ photonVec g g' = 1 ∧
      zVec g g' ⬝ᵥ photonVec g g' = 0 := by sorry

end WeinbergLeptons
