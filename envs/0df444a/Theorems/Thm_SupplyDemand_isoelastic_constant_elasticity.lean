-- Prove2me | Theorems.Thm_SupplyDemand_isoelastic_constant_elasticity
-- name    : SupplyDemand.isoelastic_constant_elasticity
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:34:15.311859+00:00
-- url     : https://prove2.me/theorems/dad1850d-ecdb-4b8c-8d2d-8f75aabdd496
-- title:
--   The isoelastic curves have constant elasticity 0.5 and −2
-- statement:
--   For every price $P>0$, the point price elasticity $\varepsilon_Q(P)=Q'(P)\,P/Q(P)$ of the source's constant-elasticity curves is constant:
--   $$\varepsilon_{S}(P)=0.5\quad\text{for } S(P)=5P^{0.5},\qquad \varepsilon_{D}(P)=-2\quad\text{for } D(P)=3P^{-2}.$$
--
--   This justifies the name "constant-elasticity" used in the source.
-- source:
--   Wikipedia, "Supply and demand", revision 1378800284, https://en.wikipedia.org/w/index.php?title=Supply_and_demand&oldid=1378800284, section "Supply schedule" and "Demand schedule" (constant-elasticity specifications)

import Mathlib
import Definitions.Def_SupplyDemand_Model

namespace SupplyDemand

theorem isoelastic_constant_elasticity (P : ℝ) (hP : 0 < P) :
    pointElasticity isoelasticSupply P = 0.5 ∧
    pointElasticity isoelasticDemand P = -2 := by sorry

end SupplyDemand
