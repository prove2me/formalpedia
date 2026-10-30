-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_N_cap_tsp
-- name    : VehicleRoutingSurvey.Routing.N_cap_tsp
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:13:44.519981+00:00
-- url     : https://prove2.me/theorems/e25b16d7-c4ad-4dee-bf83-38b3cc5d2de1
-- title:
--   Table 4, capacitated mTSP on a tree, polynomial-time algorithm
-- statement:
--   For every fixed real factor 1 <= rho < 3/2, existence of a uniform polynomial-time rho-approximation for capacitated vertex-service routing on a physical tree implies
--
--   $$\mathrm{P}=\mathrm{NP}.$$
--
--   An instance specifies a depot, positive available fleet, arbitrary nonnegative vertex demands, a capacity, and nonnegative travel weights. A feasible allocation assigns each demand whole to one depot-returning tour, respecting its capacity. The objective is the sum of tour costs, and idle vehicles are allowed.
--
--   Differences from the source:
--   - encoding: polynomial-time algorithm → one Cook-model string transducer, with decoded feasible output and cost compared with every feasible competitor; reason: the uniform polynomial bound ranges over all inputs; infeasible inputs need no approximation guarantee
--   - encoding: finite tree with numerical costs, demands, capacity and fleet data → Fin-indexed tree links with rational numerical fields and a binary fleet count; reason: retains arbitrary nonnegative unsplit demands and physical tree travel in a finite input representation
--   - reading: capacitated modification of mTSP or mCPP → m depot tours with whole-demand assignment, idle tours allowed, and sum objective; reason: retains the fleet and depot data from §2 and distinguishes service from repeat travel
--   - encoding: physical tree → connected undirected network with e+1=v; reason: for finite multigraphs this characterizes trees, including the one-vertex tree
--   - encoding: m vehicles with idle depot tours allowed → a length-prefixed list of k tours with 1 ≤ k ≤ m; the other vehicles are implicitly idle; reason: preserves the feasible service and sum objective while avoiding exponentially long output when m is binary encoded
-- source:
--   Report 7919/O, p. 6, Table 4, capacitated mTSP on a tree / polynomial-time algorithm; §4 model comments; survey [16]. Printed p. 6; PDF 8.

import Definitions.Def_VehicleRoutingSurvey_Routing_OptimizationModels

namespace VehicleRoutingSurvey.Routing

theorem N_cap_tsp :
    ∀ ρ : ℝ, 1 ≤ ρ → ρ < (3 / 2 : ℝ) →
    (∃ f, Approximation (capacitatedTree false) ρ f) → ClassesEqual := by sorry

end VehicleRoutingSurvey.Routing
