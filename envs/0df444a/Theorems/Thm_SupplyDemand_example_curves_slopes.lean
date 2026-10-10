-- Prove2me | Theorems.Thm_SupplyDemand_example_curves_slopes
-- name    : SupplyDemand.example_curves_slopes
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:17.022934+00:00
-- url     : https://prove2.me/theorems/f85838e2-8d09-47c3-ae0d-06354b61eb5e
-- title:
--   The source's example curves have the expected slopes
-- statement:
--   The four example curves of the source have the slopes the model requires:
--
--   1. the linear supply curve $Q(P)=3P-6$ is strictly increasing on $\mathbb R$;
--   2. the linear demand curve $Q(P)=32-2P$ is strictly decreasing on $\mathbb R$;
--   3. the constant-elasticity supply curve $Q(P)=5P^{0.5}$ is strictly increasing on $P>0$;
--   4. the constant-elasticity demand curve $Q(P)=3P^{-2}$ is strictly decreasing on $P>0$.
--
--   This connects the article's examples with the slope hypotheses of the comparative-statics results.
-- source:
--   Wikipedia, "Supply and demand", revision 1378800284, https://en.wikipedia.org/w/index.php?title=Supply_and_demand&oldid=1378800284, section "Supply schedule" and "Demand schedule" (example specifications)

import Mathlib
import Definitions.Def_SupplyDemand_Model

namespace SupplyDemand

theorem example_curves_slopes :
    StrictMono linearSupply ∧ StrictAnti linearDemand ∧
    StrictMonoOn isoelasticSupply (Set.Ioi 0) ∧
    StrictAntiOn isoelasticDemand (Set.Ioi 0) := by sorry

end SupplyDemand
