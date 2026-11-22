-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_weightedBlossomMatchingBlock_spec_at_entry
-- name    : VehicleRoutingSurvey.Routing.weightedBlossomMatchingBlock_spec_at_entry
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:00:17.149968+00:00
-- url     : https://prove2.me/theorems/10c459d5-2ef6-4539-9d73-4d989ef0c41d
-- title:
--   Weighted blossom matching — program refinement and cubic bound
-- statement:
--   A refinement of the fixed weighted matcher gives the compact matching execution contract with instruction constant 27648.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.weightedBlossomMatchingBlock_spec_at_entry
    (refined : ∀ {k : ℕ} {cost : Fin k → Fin k → ℝ} {s : ArithmeticState},
      CompactMateInput cost s → s.pc = 0 → s.halted = false → Nonempty (WeightedMatchingRefinement k cost s)) :
    CompactMateBlockSpec weightedBlossomMatchingBlock 27648 := by sorry
