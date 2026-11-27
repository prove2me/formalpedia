-- Prove2me | Theorems.Thm_PicardFO_Fulfill_Supplement_theorem_B_1_counterexample
-- name    : PicardFO.Fulfill.Supplement.theorem_B_1_counterexample
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T00:10:52.63757+00:00
-- url     : https://prove2.me/theorems/52b3e459-39bc-4336-852a-51a21d35259f
-- title:
--   Theorem B.1 (corrected: counterexample to 2R for numerical actions)
-- statement:
--   The printed universal bound fails for the numerical-action implementation of Algorithm 1. Take the witness data: three retailers with capacity $2$, zero demand, local fill-to-capacity policies, warehouse capacity and target $5$, threshold $2$, initial warehouse stock $5$ and empty retailers, one process per retailer, and the four orders $0,1,0,2$.
--
--   The local policies satisfy all capacity and positivity constraints, and initial stocks are valid. The sequential warehouse replenishes exactly once, so
--   $$
--   R=1,\qquad a^{\rm seq}_3=(0,0),\qquad \alpha^{2R}_3=(4,0)\ne a^{\rm seq}_3.
--   $$
--   This supplies a counterexample to Theorem B.1 on its stated domain, rather than a weakened convergence bound. It avoids both the $R=0$ boundary and low initial stock: initial warehouse stock equals $S>s$. The numeric cache cannot be identified with a reset command merely by testing its positivity. The independent local verification file checks this witness without sorry; the proposal theorem remains an open statement stub as required.
--
--   **Formalization Note** The source order $3$ is Lean order $2$. The formal certificate states both distinct exact actions along with policy admissibility, initial validity and $R=1$. It invokes the existing published cache recursion with full pairs and feasibility fallback.
--
--   Differences from the source:
--   - correction: every OWMR instance converges in at most 2R iterations → an admissible three-retailer instance with R=1 has sequential action (0,0) and cached action (4,0) at source order 3 after two iterations; reason: with zero demand, caps (5,2,2,2), s=2, S=5, initial stocks (5,0,0,0), fill-to-capacity local policies and retailer sequence 0,1,0,2, numerical replay yields cache2=[(0,2),(4,2),(4,0),(5,2)] but sequential=[(0,2),(4,2),(0,0),(0,2)]; thus the printed universal assertion is false even for positive R
--   - encoding: the sum for R runs from time 0 through T with actual orders 1 through T → the same inclusive sum with an unexecuted zero-action source-time-zero sentinel and 0-based computational orders; reason: the witness has exactly one replenishment on all actual orders; it also has no replenishment immediately beyond the horizon, so the refutation does not depend on this indexing repair
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, p. 15, Theorem B.1

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Supplement_Witness

namespace PicardFO.Fulfill.Supplement

/-- The printed 2R bound fails for numerical Algorithm 1 even with R=1 and x₁,₀=S.
The theorem certifies assumptions, count and a wrong full action after 2R sweeps. -/
theorem theorem_B_1_counterexample :
    witnessPolicy.Admissible witnessModel ∧ witnessModel.Valid witnessStock ∧
    witnessModel.replenishments witnessPolicy witnessStock witnessOrders 4 = 1 ∧
    witnessModel.sequential witnessPolicy witnessStock witnessOrders 2 = (0, 0) ∧
    witnessModel.cached witnessPolicy witnessStock witnessOrders (id : Fin 3 → Fin 3) 2 2 = (4, 0) := by sorry

end PicardFO.Fulfill.Supplement
