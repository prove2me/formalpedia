-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_N_general
-- name    : VehicleRoutingSurvey.Routing.N_general
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:13:45.658597+00:00
-- url     : https://prove2.me/theorems/ebebe992-044a-4dc8-873f-a0c250059d5f
-- title:
--   Table 4, general TSP, polynomial-time algorithm
-- statement:
--   For every fixed finite real factor rho >= 1, if general TSP has a uniform polynomial-time approximation algorithm with ratio at most rho, then
--
--   $$\mathrm{P}=\mathrm{NP}.$$
--
--   General TSP uses nonnegative symmetric weights with no triangle inequality, and a tour visits each vertex exactly once.
--
--   Differences from the source:
--   - encoding: polynomial-time algorithm → one Cook-model string transducer, with decoded feasible output and cost compared with every feasible competitor; reason: the uniform polynomial bound ranges over all inputs; infeasible inputs need no approximation guarantee
--   - encoding: general TSP with each vertex visited exactly once → permutations of Fin n with a symmetric nonnegative rational cost matrix and no triangle inequality; reason: the finite matrix encodes the undirected general TSP; a singleton has an idle tour, and diagonal entries are unused
-- source:
--   Report 7919/O, p. 6, Table 4, general TSP / polynomial-time algorithm; §4 model comments; survey [33]. Printed p. 6; PDF 8.

import Definitions.Def_VehicleRoutingSurvey_Routing_OptimizationModels

namespace VehicleRoutingSurvey.Routing

theorem N_general :
    ∀ ρ : ℝ, 1 ≤ ρ →
    (∃ f, Approximation generalTSP ρ f) → ClassesEqual := by sorry

end VehicleRoutingSurvey.Routing
