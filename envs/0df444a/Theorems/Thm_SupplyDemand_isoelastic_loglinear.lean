-- Prove2me | Theorems.Thm_SupplyDemand_isoelastic_loglinear
-- name    : SupplyDemand.isoelastic_loglinear
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:47.472605+00:00
-- url     : https://prove2.me/theorems/ef8b5600-6ab6-48ae-a0d4-6bffa66598f8
-- title:
--   Log-linear form of the isoelastic curves
-- statement:
--   For every price $P>0$,
--   $$\log\big(5P^{0.5}\big)=\log 5+0.5\log P\qquad\text{and}\qquad\log\big(3P^{-2}\big)=\log 3-2\log P.$$
--
--   These are the source's rewritings of the constant-elasticity supply and demand functions as log-log (log-linear) functions.
--
--   **Formalization Note** $\log$ is the natural logarithm; the restriction $P>0$ is where the source's formulas are meaningful.
-- source:
--   Wikipedia, "Supply and demand", revision 1378800284, https://en.wikipedia.org/w/index.php?title=Supply_and_demand&oldid=1378800284, section "Supply schedule" and "Demand schedule" (constant-elasticity specifications)

import Mathlib
import Definitions.Def_SupplyDemand_Model

namespace SupplyDemand

theorem isoelastic_loglinear (P : ℝ) (hP : 0 < P) :
    Real.log (isoelasticSupply P) = Real.log 5 + 0.5 * Real.log P ∧
    Real.log (isoelasticDemand P) = Real.log 3 - 2 * Real.log P := by sorry

end SupplyDemand
