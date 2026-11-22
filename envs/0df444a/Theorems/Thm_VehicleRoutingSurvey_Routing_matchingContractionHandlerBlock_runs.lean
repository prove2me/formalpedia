-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_matchingContractionHandlerBlock_runs
-- name    : VehicleRoutingSurvey.Routing.matchingContractionHandlerBlock_runs
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:00:22.41074+00:00
-- url     : https://prove2.me/theorems/04cced64-1c28-4623-8596-c674c0ef137e
-- title:
--   Weighted blossom matching — contraction handler execution
-- statement:
--   The contraction handler executes its structure and cache-repair blocks with the stated instruction bound.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.matchingContractionHandlerBlock_runs (s : ArithmeticState) (layout : MatchingContractionLayout s)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t ticks, ticks ≤ (300 * s.nr 55 + 110) * (1 + t.nr 87 + t.nr 99) ∧
      BlockRuns matchingContractionHandlerBlock ticks s t ∧ t.halted = false ∧ t.nr 87 ≤ s.nr 55 ∧
      t.nr 1 = 0 ∧ t.nr 3 = s.nr 58 ∧ t.nr 4 = s.nr 59 ∧ t.nr 5 = s.nr 60 ∧ t.nr 8 = s.nr 61 ∧
      t.rr 15 = s.rr 15 + s.rr 1 ∧ (∀ a < s.nr 51, t.nm a = s.nm a) ∧
      (∀ a < s.nr 62, t.rm a = s.rm a) ∧
      ∀ r ≥ 30, r ∉ [68, 76, 81, 82, 87, 99] → t.nr r = s.nr r := by sorry
