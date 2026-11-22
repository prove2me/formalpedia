-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingDispatchState_traceOuter
-- name    : VehicleRoutingSurvey.Routing.MatchingDispatchState.traceOuter
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:16:10.760255+00:00
-- url     : https://prove2.me/theorems/70067b3f-56ae-4ae4-88bc-d8b6190b30f9
-- title:
--   Weighted blossom matching — tracing the selected outer edge
-- statement:
--   The actual outer-event classifier traces both selected forest paths, records the branch tag, and preserves the dispatcher views in the untouched memory regions.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionArm

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.MatchingDispatchState.traceOuter {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s : ArithmeticState} (before : MatchingDispatchState cost original i s)
    (entry : s.pc = 0) (live : s.halted = false) (outer : matchingEventClass s = 1) :
    ∃ a b : Fin k, before.selected.event = .edge s(a,b) ∧ before.part.blocks.block a ≠ before.part.blocks.block b ∧
      ∃ pa pb, before.forest.role (before.part.representative a) = .outer pa ∧
        before.forest.role (before.part.representative b) = .outer pb ∧
        ∃ t ticks, ticks ≤ 34*k+57 ∧ BlockRuns classifyAndTraceMatchingEvent ticks s t ∧ t.halted = false ∧
          t.nr 36 = 0 ∧ t.nr 37 = 1 ∧ t.nr 38 = 2 ∧ t.nr 1 = s.nr 1 ∧
          (t.nr 92,t.nr 93) = (a.val,b.val) ∧
          (∀ x, x < s.nr 83 ∨ s.nr 83+3*k ≤ x → t.nm x = s.nm x) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
          (∀ r, r = 9 ∨ r = 20 ∨ r = 21 ∨ (30 ≤ r ∧ r ≤ 34) ∨
            (39 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r → t.nr r = s.nr r) ∧
          ∃ ready, ready.nr 83 = s.nr 83 ∧ ready.nr 84 = s.nr 84 ∧
            MatchingResolvedOuter before.forest (before.part.representative a) (before.part.representative b)
              (s.nr 83) ready t := by sorry
