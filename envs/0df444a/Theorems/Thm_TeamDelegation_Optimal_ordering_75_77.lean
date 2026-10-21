-- Prove2me | Theorems.Thm_TeamDelegation_Optimal_ordering_75_77
-- name    : TeamDelegation.Optimal.ordering_75_77
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:20.530856+00:00
-- url     : https://prove2.me/theorems/e546ef03-dd24-4e1d-b317-e234cda80fa2
-- title:
--   Equations (75)–(77): cost-saving and surplus thresholds overlap
-- statement:
--   Under the standing assumptions and Assumption 1, the aggregate-cost threshold lies strictly above the lower surplus threshold and below both upper surplus thresholds:
--
--   $$\widetilde\Delta_{\mathrm{sum}}^1<\Delta_{\mathrm{sum}}^*<\min\{\widetilde\Delta_{\mathrm{sum}}^2,\widetilde\Delta_{\mathrm{sum}}^3\},\qquad
--   0<\Delta_{\mathrm{sum}}^*<\Delta_A^{\mathrm{crit}}+\Delta_B^{\max}.$$
--
--   These strict orderings make a nonempty range of aggregate adoption-cost differences compatible with lower delegated wage cost and maximal agent surplus.
--
--   **Formalization Note** Equation (75) prints a minus sign before $(1-r)q_0$ where its preceding definitions require a plus sign. The theorem states the paper's threshold ordering, without copying that intermediate typo.
-- source:
--   Upton, Implicit Incentives and Delegation in Teams, TRR 266 Working Paper No. 67 (SSRN 3991736, 17 Dec 2021), p. 39 (PDF 40), equations (75)–(77) and following interval paragraph

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model

namespace TeamDelegation.Optimal

/-- Equations (75)–(77) and the following paragraph, p. 39: the
cost-saving bound lies strictly between the surplus bounds and within the feasible range. -/
theorem ordering_75_77 (P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) :
    DeltaTilde1 P < DeltaStarSum P ∧
      DeltaStarSum P < DeltaTilde2 P ∧
      DeltaStarSum P < DeltaTilde3 P ∧
      0 < DeltaStarSum P ∧
      DeltaStarSum P < DeltaCritA P + DeltaMaxB P := by sorry

end TeamDelegation.Optimal
