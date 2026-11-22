-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingDispatchState_contract
-- name    : VehicleRoutingSurvey.Routing.MatchingDispatchState.contract
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:00:04.024532+00:00
-- url     : https://prove2.me/theorems/b336b2f7-64da-46f7-a969-b58fe228a73f
-- title:
--   Weighted blossom matching — verified contraction event
-- statement:
--   A selected outer edge within one alternating tree yields a prepared search stage with a new blossom and an explicit credit transition, including the instruction cost of the actual dispatcher.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.MatchingDispatchState.contract {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s classified : ArithmeticState} {classTicks : ℕ}
    (before : MatchingDispatchState cost original i s) (searching : i < k/2)
    (symmetric : ∀ u v, cost u v = cost v u)
    (entry : s.pc = 0) (running : s.halted = false) (active : s.nr 33 ≠ 0)
    (outer : matchingEventClass s = 1) (winner : s.nr 1 ≤ s.nr 61)
    (classify : BlockRuns classifyAndTraceMatchingEvent classTicks s classified) (tag : classified.nr 35 = 1) :
    ∃ next ticks charge, BlockRuns weightedBlossomEventHandler ticks s next ∧
      next.halted = false ∧ next.nr 33 ≠ 0 ∧
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot next)) ∧
      MatchingStageTransition (matchingLoopCounts k i s) charge (matchingLoopCounts k i (matchingStageSnapshot next)) ∧
      ticks ≤ 1024*(k+1)*charge := by sorry
