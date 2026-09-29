-- Prove2me | Theorems.Thm_WeinbergLeptons_couplings_exceed_charge
-- name    : WeinbergLeptons.couplings_exceed_charge
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T18:47:11.177996+00:00
-- url     : https://prove2.me/theorems/143d9cd2-0bd6-4381-a946-855233022d73
-- title:
--   The gauge couplings $g$ and $g'$ are larger than $e$
-- statement:
--   Let $g,g'$ be nonzero reals and $e=gg'/(g^2+g'^2)^{1/2}$. Then
--
--   $$|e|<|g|\quad\text{and}\quad|e|<|g'|.$$
-- source:
--   S. Weinberg, A Model of Leptons, Phys. Rev. Lett. 19, 1264-1266 (1967), https://doi.org/10.1103/PhysRevLett.19.1264, p. 1265, text following eq. (16)

import Definitions.Def_WeinbergLeptons_Model

open Matrix

namespace WeinbergLeptons

theorem couplings_exceed_charge (g g' : ℝ) (hg : g ≠ 0) (hg' : g' ≠ 0) :
    |electricCharge g g'| < |g| ∧ |electricCharge g g'| < |g'| := by sorry

end WeinbergLeptons
