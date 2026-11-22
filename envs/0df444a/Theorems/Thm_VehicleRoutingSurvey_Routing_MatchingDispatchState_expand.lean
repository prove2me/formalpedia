-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingDispatchState_expand
-- name    : VehicleRoutingSurvey.Routing.MatchingDispatchState.expand
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:01:47.468427+00:00
-- url     : https://prove2.me/theorems/afac22f3-df05-4c96-9c24-6b221f9df48a
-- title:
--   Weighted blossom matching — verified expansion event
-- statement:
--   A selected tight blossom expansion yields a new prepared search stage, with a credit transition and a bound on the dispatcher instructions.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.MatchingDispatchState.expand {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s : ArithmeticState} (before : MatchingDispatchState cost original i s)
    (searching : i < k/2) (symmetric : ∀ u v, cost u v = cost v u)
    (entry : s.pc = 0) (running : s.halted = false) (active : s.nr 33 ≠ 0)
    (expand : matchingEventClass s = 2) :
    ∃ next ticks charge, BlockRuns weightedBlossomEventHandler ticks s next ∧
      next.halted = false ∧ next.nr 33 ≠ 0 ∧
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot next)) ∧
      MatchingStageTransition (matchingLoopCounts k i s) charge (matchingLoopCounts k i (matchingStageSnapshot next)) ∧
      ticks ≤ 1024*(k+1)*charge := by sorry
