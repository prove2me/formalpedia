-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingDispatchState_augment
-- name    : VehicleRoutingSurvey.Routing.MatchingDispatchState.augment
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:00:17.193307+00:00
-- url     : https://prove2.me/theorems/2b45e265-37dd-4d05-8f86-7f557d9f5203
-- title:
--   Weighted blossom matching — verified augmentation event
-- statement:
--   When a selected outer edge connects distinct alternating trees, the dispatcher augments the matching, terminates the current stage, and returns the invariant for the next stage within its instruction budget.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.MatchingDispatchState.augment {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s classified : ArithmeticState} {classTicks : ℕ}
    (before : MatchingDispatchState cost original i s) (searching : i < k/2)
    (entry : s.pc = 0) (running : s.halted = false) (outer : matchingEventClass s = 1)
    (winner : s.nr 1 ≤ s.nr 61)
    (classify : BlockRuns classifyAndTraceMatchingEvent classTicks s classified) (tag : classified.nr 35 = 3) :
    ∃ next ticks, BlockRuns weightedBlossomEventHandler ticks s next ∧
      next.halted = false ∧ next.nr 33 = 0 ∧
      Nonempty (MatchingBetweenStages cost original (i+1) (matchingStageSnapshot next)) ∧
      ticks ≤ 512 * (k^2+1) := by sorry
