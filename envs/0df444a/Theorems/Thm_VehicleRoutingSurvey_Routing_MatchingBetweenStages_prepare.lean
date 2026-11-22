-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingBetweenStages_prepare
-- name    : VehicleRoutingSurvey.Routing.MatchingBetweenStages.prepare
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:00:30.839084+00:00
-- url     : https://prove2.me/theorems/177d6956-3345-480d-aa9b-8abb2b4e317c
-- title:
--   Weighted blossom matching — preparing a search stage
-- statement:
--   A valid state between weighted matching stages yields a prepared search state, with the required candidate memory and instruction budget.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.MatchingBetweenStages.prepare {k i : ℕ} {cost : Fin k → Fin k → ℝ} {original s : ArithmeticState}
    (old : MatchingBetweenStages cost original i (matchingLoopSnapshot s)) (before : i < k/2)
    (input : CompactMateInput cost original) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t steps, steps ≤ 104*k*k+48*k+33 ∧ BlockRuns prepareWeightedMatchingStageBlock steps s t ∧
      t.halted = false ∧ t.nr 31 = 6*k+1 ∧ t.nr 32 = 0 ∧ t.nr 33 = 1 ∧ t.nr 34 = 1 ∧
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot t)) ∧
      (matchingStageCountsFromRAM k (matchingStageSnapshot t) ((matchingStageSnapshot t).nr 39)).credit ≤ 6*k := by sorry
