-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_matchingContractionStructure_spec
-- name    : VehicleRoutingSurvey.Routing.matchingContractionStructure_spec
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:00:27.909653+00:00
-- url     : https://prove2.me/theorems/9c05e004-58fd-44e6-b30b-138d3c99f879
-- title:
--   Weighted blossom matching — contraction structure
-- statement:
--   The contraction structure block advances the dual values and writes the new odd-cycle record with the required memory layout.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.matchingContractionStructure_spec (s : ArithmeticState) (layout : MatchingContractionLayout s)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t ticks, ticks ≤ 120 * s.nr 55 + 78 ∧ BlockRuns matchingContractionStructure ticks s t ∧
      t.halted = false ∧ t.nr 87 ≤ s.nr 55 ∧ t.rr 15 = s.rr 15 + s.rr 1 ∧
      (∀ a < s.nr 51, t.nm a = s.nm a) ∧ (∀ a < s.nr 62, t.rm a = s.rm a) ∧
      (∀ r, r ∉ [0, 6, 7, 10, 11, 15, 16, 17, 18, 19, 23, 68, 76, 81, 82, 87, 99] → t.nr r = s.nr r) ∧
      t.rm = Function.update (iterateBlossomDuals {s with rm := advancedEffectiveMemory s} (s.nr 55))
        (s.nr 75+s.nr 76) 0 ∧
      (s.nr 52+s.nr 55 ≤ s.nr 86 → s.nr 74+s.nr 55 ≤ s.nr 86 → MatchingContractionPrefixView s t) := by sorry
