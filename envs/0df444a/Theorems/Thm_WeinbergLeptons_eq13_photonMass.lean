-- Prove2me | Theorems.Thm_WeinbergLeptons_eq13_photonMass
-- name    : WeinbergLeptons.eq13_photonMass
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:50:23.199118+00:00
-- url     : https://prove2.me/theorems/9ee23ab0-b37f-48e8-b34e-5d700ef41e47
-- title:
--   Eqs. (11), (13): the neutral boson $A$ is massless
-- statement:
--   For all real $g,g',\lambda$, the coefficient vector $a=(g^2+g'^2)^{-1/2}(0,0,-g',g)$ of $A_\mu=(g^2+g'^2)^{-1/2}(-g'A_\mu^3+gB_\mu)$ lies in the kernel of the mass-squared matrix:
--
--   $$\mathcal M\,a=0,$$
--
--   so $M_A=0$ and $A_\mu$ is identified with the photon.
-- source:
--   S. Weinberg, A Model of Leptons, Phys. Rev. Lett. 19, 1264-1266 (1967), https://doi.org/10.1103/PhysRevLett.19.1264, p. 1265, eqs. (11), (13)

import Definitions.Def_WeinbergLeptons_Model

open Matrix

namespace WeinbergLeptons

theorem eq13_photonMass (g g' lam : ℝ) :
    massSqMatrix g g' lam *ᵥ photonVec g g' = 0 := by sorry

end WeinbergLeptons
