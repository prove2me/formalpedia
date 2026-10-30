-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_A14_upper
-- name    : VehicleRoutingSurvey.Routing.A14_upper
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:13:41.603225+00:00
-- url     : https://prove2.me/theorems/15708c11-0bea-4aba-9b27-fd0bdf18056f
-- title:
--   Table 3, MCPP, mixed strategy, upper cell
-- statement:
--   On every strongly connected mixed network with nonnegative real weights and every link required, every admissible combined mixed strategy run has cost C satisfying
--
--   $$C\le 5/3\,\mathrm{OPT}.$$
--
--   The algorithm has a run on each instance and its output is a feasible closed service walk. The cost inequality also covers OPT = 0.
--
--   Differences from the source:
--   - reading: the named heuristic without pseudocode in the survey → the concrete combined mixed strategy run relation, identified in survey reference [9], §§3–5; reason: fixes the named procedure independently of its performance bound, retaining arbitrary legitimate ties
-- source:
--   Report 7919/O, p. 5, Table 3, MCPP / mixed strategy, upper cell; §4 pp. 4, 6; survey [9]. Printed p. 5; PDF 7. Algorithm definition: survey [9], Frederickson (1979), §§3–5, pp. 540–547; https://www.scribd.com/document/930249049/322139-322150.

import Definitions.Def_VehicleRoutingSurvey_Routing_MixedAlgorithms

namespace VehicleRoutingSurvey.Routing

theorem A14_upper :
    ∀ (I : Service), MixedPostman I →
    (∃ u ts, GeneralMixedRun I.graph u ts) ∧
    ∀ (u : Fin I.graph.n) (ts : List (Traversal I.graph)), GeneralMixedRun I.graph u ts →
      Feasible I u ts ∧ pathCost I.graph ts ≤ (5 / 3 : ℝ) * optimum I := by sorry

end VehicleRoutingSurvey.Routing
