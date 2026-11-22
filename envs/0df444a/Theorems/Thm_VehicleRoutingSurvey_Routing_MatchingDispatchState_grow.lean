-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingDispatchState_grow
-- name    : VehicleRoutingSurvey.Routing.MatchingDispatchState.grow
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T15:23:36.759358+00:00
-- url     : https://prove2.me/theorems/03f5a4c0-8a6f-424c-b6bc-cc705d13b08a
-- title:
--   Weighted blossom matching — verified growth event
-- statement:
--   Consider stage $i<k/2$ of the weighted matching algorithm on $k$ compact vertices with symmetric costs. If the selected event is growth and the dispatcher enters in a valid, active state, executing its actual instruction block produces a new active, prepared search state. The execution takes at most $1024(k+1)$ times its charge, and the counters before and after the event satisfy the matching stage credit transition.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface

open VehicleRoutingSurvey.Routing

theorem VehicleRoutingSurvey.Routing.MatchingDispatchState.grow {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s : ArithmeticState} (before : MatchingDispatchState cost original i s)
    (searching : i < k/2) (symmetric : ∀ u v, cost u v = cost v u)
    (entry : s.pc = 0) (running : s.halted = false)
    (active : s.nr 33 ≠ 0) (grow : matchingEventClass s = 0) :
    ∃ next ticks charge, BlockRuns weightedBlossomEventHandler ticks s next ∧
      next.halted = false ∧ next.nr 33 ≠ 0 ∧
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot next)) ∧
      MatchingStageTransition (matchingLoopCounts k i s) charge (matchingLoopCounts k i (matchingStageSnapshot next)) ∧
      ticks ≤ 1024 * (k+1) * charge := by sorry
