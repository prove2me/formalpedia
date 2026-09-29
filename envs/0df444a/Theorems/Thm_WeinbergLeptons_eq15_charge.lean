-- Prove2me | Theorems.Thm_WeinbergLeptons_eq15_charge
-- name    : WeinbergLeptons.eq15_charge
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:57:34.416225+00:00
-- url     : https://prove2.me/theorems/49aeab17-d4a0-4fbb-af35-39bee2efe3c3
-- title:
--   Eq. (15): the rationalized electric charge $e=gg'/(g^2+g'^2)^{1/2}$
-- statement:
--   Let $g,g'$ be real with $g^2+g'^2>0$. For a field with weak isospin component $T_3$ and hypercharge $Y$ (charge $Q=T_3-Y$ in the conventions of the paper), the neutral gauge coupling $gT_3A^3+g'YB$ decomposes along the photon and $Z$ as
--
--   $$gT_3A^3+g'YB=-e\,Q\,A+\frac{g^2T_3+g'^2Y}{(g^2+g'^2)^{1/2}}\,Z,\qquad e=\frac{gg'}{(g^2+g'^2)^{1/2}},$$
--
--   for all real $T_3,Y$ and all field values, where $A$ and $Z$ are the combinations (11) and (10). Hence the photon couples to the charge with strength $e$.
-- source:
--   S. Weinberg, A Model of Leptons, Phys. Rev. Lett. 19, 1264-1266 (1967), https://doi.org/10.1103/PhysRevLett.19.1264, p. 1264 (definitions of $Q$, $Y$) and p. 1265, eqs. (14), (15)

import Definitions.Def_WeinbergLeptons_Model

open Matrix

namespace WeinbergLeptons

theorem eq15_charge (g g' : ℝ) (hN : 0 < g ^ 2 + g' ^ 2) (T3 Y : ℝ) (V : Fin 4 → ℝ) :
    g * T3 * V 2 + g' * Y * V 3 =
      -electricCharge g g' * (T3 - Y) * (photonVec g g' ⬝ᵥ V) +
        (g ^ 2 * T3 + g' ^ 2 * Y) / Real.sqrt (g ^ 2 + g' ^ 2) * (zVec g g' ⬝ᵥ V) := by sorry

end WeinbergLeptons
