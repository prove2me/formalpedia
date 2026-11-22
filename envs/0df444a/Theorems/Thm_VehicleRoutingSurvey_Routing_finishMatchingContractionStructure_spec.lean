-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_finishMatchingContractionStructure_spec
-- name    : VehicleRoutingSurvey.Routing.finishMatchingContractionStructure_spec
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:12:17.985472+00:00
-- url     : https://prove2.me/theorems/b5d24076-1dae-4f99-bd45-f49ec13750a5
-- title:
--   Weighted blossom matching — completing the contraction structure
-- statement:
--   The second portion of the contraction structure writes the cycle, changes the representatives, and returns the typed memory view and cost bound.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionStructure

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.finishMatchingContractionStructure_spec (s : ArithmeticState) (layout : MatchingContractionLayout s)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    ∃ t ticks, ticks ≤ 89 * s.nr 55 + 67 ∧ BlockRuns finishMatchingContractionStructure ticks s t ∧
      t.halted = false ∧ t.nr 87 ≤ s.nr 55 ∧
      (∀ a < s.nr 51, t.nm a = s.nm a) ∧ (∀ a < s.nr 62, t.rm a = s.rm a) ∧
      (∀ r, r ∉ [0, 6, 7, 10, 11, 15, 16, 17, 18, 19, 23, 68, 76, 87, 99] → t.nr r = s.nr r) ∧
      t.rm = startMatchingCycleReal s ∧
      (s.nr 52+s.nr 55 ≤ s.nr 86 → s.nr 74+s.nr 55 ≤ s.nr 86 → MatchingContractionPrefixView s t) := by sorry
