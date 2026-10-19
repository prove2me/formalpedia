-- Prove2me | Theorems.Thm_StrategicPolicy_NonMonotone_cost_not_om
-- name    : StrategicPolicy.NonMonotone.cost_not_om
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T14:40:16.221035+00:00
-- url     : https://prove2.me/theorems/22f98d42-27c2-43e7-bc13-fb9ce252ba08
-- title:
--   Section 5, p. 9 — the example's cost is not outcome monotonic
-- statement:
--   In the three-value instance of Section 5, the cost matrix does not satisfy the paper's outcome-monotonicity condition:
--
--   $$
--   \neg\operatorname{OMCost}(q,c).
--   $$
--
--   In particular, moving from $x_1$ to the lower-outcome value $x_2$ costs $0.2$ rather than zero. This identifies the change from the outcome-monotonic-cost regime considered in Section 4.
--
--   **Formalization Note** The paper's zero-cost biconditional is applied only to distinct feature values, while staying costs zero, as explained in the mission scope.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 9, §5 paragraph before the general-cost matrix; p. 6, §4 outcome-monotonic cost definition

import Mathlib
import Definitions.Def_StrategicPolicy_NonMonotone_Setting
import Definitions.Def_StrategicPolicy_NonMonotone_Example

namespace StrategicPolicy.NonMonotone

/-- Section 5, page 9: the example's cost violates outcome monotonicity. -/
theorem cost_not_om : ¬ StrategicPolicy.StochasticOpt.OMCost q c := by sorry

end StrategicPolicy.NonMonotone
