-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_A12_upper
-- name    : VehicleRoutingSurvey.Routing.A12_upper
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:13:26.651403+00:00
-- url     : https://prove2.me/theorems/f1ef9134-e0b0-4b9d-969a-ee7527e78023
-- title:
--   Table 3, MCPP, Edmonds-Johnson, upper cell
-- statement:
--   On every strongly connected mixed network with nonnegative real weights and every link required, every admissible Edmonds–Johnson run has cost C satisfying
--
--   $$C\le 2\,\mathrm{OPT}.$$
--
--   The algorithm has a run on each instance and its output is a feasible closed service walk. The cost inequality also covers OPT = 0.
--
--   Differences from the source:
--   - reading: the named heuristic without pseudocode in the survey → the concrete Edmonds–Johnson run relation, identified in survey reference [9], §§3–5; reason: fixes the named procedure independently of its performance bound, retaining arbitrary legitimate ties
-- source:
--   Report 7919/O, p. 5, Table 3, MCPP / Edmonds-Johnson, upper cell; §4 pp. 4, 6; survey [9]. Printed p. 5; PDF 7. Algorithm definition: survey [9], Frederickson (1979), §§3–5, pp. 540–547; https://www.scribd.com/document/930249049/322139-322150.

import Definitions.Def_VehicleRoutingSurvey_Routing_MixedAlgorithms

namespace VehicleRoutingSurvey.Routing

theorem A12_upper :
    ∀ (I : Service), MixedPostman I →
    (∃ u ts, MixedOneRun I.graph u ts) ∧
    ∀ (u : Fin I.graph.n) (ts : List (Traversal I.graph)), MixedOneRun I.graph u ts →
      Feasible I u ts ∧ pathCost I.graph ts ≤ (2 : ℝ) * optimum I := by sorry

end VehicleRoutingSurvey.Routing
