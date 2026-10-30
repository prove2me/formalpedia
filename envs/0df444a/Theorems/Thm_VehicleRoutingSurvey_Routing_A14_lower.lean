-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_A14_lower
-- name    : VehicleRoutingSurvey.Routing.A14_lower
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:13:18.006862+00:00
-- url     : https://prove2.me/theorems/30b9b808-1d24-4ae2-b330-503ddf6003ea
-- title:
--   Table 3, MCPP, mixed strategy, lower cell
-- statement:
--   For every epsilon > 0 and vertex threshold N, there is a strongly connected mixed postman network with v >= N, positive optimum OPT, and an admissible combined mixed strategy run whose cost C satisfies
--
--   $$C>(3/2-\varepsilon)\,\mathrm{OPT}.$$
--
--   This is the asymptotic lower cell of Table 3. It concerns this same algorithm and permits witnesses on an unbounded subsequence of sizes.
--
--   Differences from the source:
--   - reading: the named heuristic without pseudocode in the survey → the concrete combined mixed strategy run relation, identified in survey reference [9], §§3–5; reason: fixes the named procedure independently of its performance bound, retaining arbitrary legitimate ties
--   - encoding: asymptotic bad instances, deleting vanishing terms → for every positive epsilon and size threshold, a larger positive-OPT instance exceeds the displayed bound minus epsilon; reason: arbitrarily large witnesses preserve the report convention without asserting a witness at every size
-- source:
--   Report 7919/O, p. 5, Table 3, MCPP / mixed strategy, lower cell; §4 pp. 4, 6; survey [9]. Printed p. 5; PDF 7. Algorithm definition: survey [9], Frederickson (1979), §§3–5, pp. 540–547; https://www.scribd.com/document/930249049/322139-322150.

import Definitions.Def_VehicleRoutingSurvey_Routing_MixedAlgorithms

namespace VehicleRoutingSurvey.Routing

theorem A14_lower :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ (I : Service) (u : Fin I.graph.n) (ts : List (Traversal I.graph)),
      MixedPostman I ∧ N ≤ I.graph.n ∧ 0 < optimum I ∧ GeneralMixedRun I.graph u ts ∧
      (3 / 2 - ε) * optimum I < pathCost I.graph ts := by sorry

end VehicleRoutingSurvey.Routing
