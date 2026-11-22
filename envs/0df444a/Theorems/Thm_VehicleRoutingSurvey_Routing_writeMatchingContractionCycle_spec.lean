-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_writeMatchingContractionCycle_spec
-- name    : VehicleRoutingSurvey.Routing.writeMatchingContractionCycle_spec
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:12:18.607176+00:00
-- url     : https://prove2.me/theorems/629e3b35-136d-46c6-a475-57b754c6ddc6
-- title:
--   Weighted blossom matching — writing the contraction cycle
-- statement:
--   The cycle writer emits the archived edge records at the expected addresses and preserves the stated memory regions.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionStructure

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.writeMatchingContractionCycle_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 26 * (s.nr 13 + s.nr 14) + 34 ∧ BlockRuns writeMatchingContractionCycle steps s t ∧
      t.halted = false ∧ t.nr 68 = s.nr 68 + 4 * matchingCycleChildCount s ∧
      (∀ a < s.nr 68, t.nm a = startMatchingCycleNat s a) ∧ t.rm = startMatchingCycleReal s ∧
      (∀ r, r ∉ [0, 6, 7, 10, 15, 16, 17, 18, 23, 68] → t.nr r = s.nr r) ∧
      (MatchingCycleReadSafety (matchingCycleRecordReference s) →
        (∀ j < s.nr 13, matchingCycleChildAt t.nm (s.nr 68 + 4 * j) = leftCycleRecordAt (matchingCycleRecordReference s) j) ∧
        matchingCycleChildAt t.nm (s.nr 68 + 4 * s.nr 13) = commonCycleRecord (matchingCycleRecordReference s) ∧
        ∀ j < s.nr 14, matchingCycleChildAt t.nm (s.nr 68 + 4 * (s.nr 13 + 1 + j)) = rightCycleRecordAt (matchingCycleRecordReference s) j) := by sorry
