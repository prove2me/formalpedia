-- Prove2me | Theorems.Thm_WeinbergLeptons_eq7_massTerm
-- name    : WeinbergLeptons.eq7_massTerm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:26:12.643758+00:00
-- url     : https://prove2.me/theorems/b14d5277-4061-492b-96d4-a524afb819e4
-- title:
--   Eq. (7): spin-one mass terms as a quadratic form
-- statement:
--   For all real $g,g',\lambda$ and every gauge-field configuration $V=(A^1,A^2,A^3,B)$,
--
--   $$-\tfrac18\lambda^2g^2[(A^1)^2+(A^2)^2]-\tfrac18\lambda^2(gA^3+g'B)^2=-\tfrac12\,V^{\mathsf T}\mathcal M V,$$
--
--   where $\mathcal M$ is the mass-squared matrix of the model. This identifies $\mathcal M$ as the (mass)$^2$ matrix of the spin-one fields read off from eq. (7).
-- source:
--   S. Weinberg, A Model of Leptons, Phys. Rev. Lett. 19, 1264-1266 (1967), https://doi.org/10.1103/PhysRevLett.19.1264, p. 1265, eq. (7)

import Definitions.Def_WeinbergLeptons_Model

open Matrix

namespace WeinbergLeptons

theorem eq7_massTerm (g g' lam : ℝ) (V : Fin 4 → ℝ) :
    vectorMassTerm g g' lam V = -(1 / 2) * (V ⬝ᵥ (massSqMatrix g g' lam *ᵥ V)) := by sorry

end WeinbergLeptons
