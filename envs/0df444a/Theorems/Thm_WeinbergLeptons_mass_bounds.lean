-- Prove2me | Theorems.Thm_WeinbergLeptons_mass_bounds
-- name    : WeinbergLeptons.mass_bounds
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:00:53.007242+00:00
-- url     : https://prove2.me/theorems/0fc3abdb-2877-4ac5-b32f-14f8ce755fde
-- title:
--   Lower bounds on $M_W$ and $M_Z$ ($M_W>40$ BeV, $M_Z>M_W$, $M_Z>80$ BeV)
-- statement:
--   Let $g,g',\lambda$ be nonzero reals, $e=gg'/(g^2+g'^2)^{1/2}$, $M_W=\tfrac12\lambda g$, $M_Z=\tfrac12\lambda(g^2+g'^2)^{1/2}$, and $G_W$ as in eq. (16). Then
--
--   1. $M_W^2>\dfrac{\sqrt2\,e^2}{8G_W}$;
--   2. $M_Z^2>M_W^2$;
--   3. $M_Z^2\ge4\cdot\dfrac{\sqrt2\,e^2}{8G_W}$.
--
--   With the measured $e$ and $G_W$, $\big(\sqrt2e^2/8G_W\big)^{1/2}$ is the paper's '40 BeV', so these are the parameter-free forms of $M_W>40$ BeV, $M_Z>M_W$ and $M_Z>80$ BeV.
--
--   **Formalization Note** The numerical values are not formalized; the third bound is non-strict (equality at $|g|=|g'|$).
-- source:
--   S. Weinberg, A Model of Leptons, Phys. Rev. Lett. 19, 1264-1266 (1967), https://doi.org/10.1103/PhysRevLett.19.1264, p. 1265, text following eq. (16)

import Definitions.Def_WeinbergLeptons_Model

open Matrix

namespace WeinbergLeptons

theorem mass_bounds (g g' lam : ℝ) (hg : g ≠ 0) (hg' : g' ≠ 0) (hlam : lam ≠ 0) :
    Real.sqrt 2 * electricCharge g g' ^ 2 / (8 * weakCoupling g lam) < wMass g lam ^ 2 ∧
      wMass g lam ^ 2 < zMass g g' lam ^ 2 ∧
      4 * (Real.sqrt 2 * electricCharge g g' ^ 2 / (8 * weakCoupling g lam)) ≤ zMass g g' lam ^ 2 := by sorry

end WeinbergLeptons
