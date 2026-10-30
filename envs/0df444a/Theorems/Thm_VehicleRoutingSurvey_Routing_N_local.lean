-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_N_local
-- name    : VehicleRoutingSurvey.Routing.N_local
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:13:39.419914+00:00
-- url     : https://prove2.me/theorems/2b8868cb-4735-4dfe-b363-2aac425f63a5
-- title:
--   Table 4, general TSP, local search with polynomial time per iteration
-- statement:
--   For every fixed finite real factor rho >= 1, if general TSP has a local-search rule polynomial per iteration such that every local optimum has cost at most rho times the global optimum, then
--
--   $$\mathrm{P}=\mathrm{NP}.$$
--
--   General TSP uses nonnegative symmetric weights with no triangle inequality, and a tour visits each vertex exactly once.
--
--   Differences from the source:
--   - encoding: polynomial time per local-search iteration → one Cook transducer returns an improving feasible neighbor or a correct no-improvement flag; reason: time is bounded per invocation on the instance and current tour; no total-iteration bound is asserted
--   - encoding: general TSP with each vertex visited exactly once → permutations of Fin n with a symmetric nonnegative rational cost matrix and no triangle inequality; reason: the finite matrix encodes the undirected general TSP; a singleton has an idle tour, and diagonal entries are unused
--   - reading: local search polynomial per iteration → one uniform polynomial-time improving-neighbor-or-local-optimality operation on instance and tour codes; reason: makes effectiveness explicit without assuming a polynomial number of iterations
-- source:
--   Report 7919/O, p. 6, Table 4, general TSP / local search with polynomial time per iteration; §4 model comments; survey [29]. Printed p. 6; PDF 8.

import Definitions.Def_VehicleRoutingSurvey_Routing_OptimizationModels

namespace VehicleRoutingSurvey.Routing

theorem N_local :
    ∀ ρ : ℝ, 1 ≤ ρ →
    (∃ neighbor step, EffectiveLocalSearch generalTSP neighbor step ∧
      ∀ x y, generalTSP.valid x → LocalOptimum generalTSP neighbor x y →
        ∀ z, generalTSP.feasible x z →
          (generalTSP.cost x y : ℝ) ≤ ρ * (generalTSP.cost x z : ℝ)) → ClassesEqual := by sorry

end VehicleRoutingSurvey.Routing
