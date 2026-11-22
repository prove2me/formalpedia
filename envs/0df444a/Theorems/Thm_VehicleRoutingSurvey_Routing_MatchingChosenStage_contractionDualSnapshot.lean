-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingChosenStage_contractionDualSnapshot
-- name    : VehicleRoutingSurvey.Routing.MatchingChosenStage.contractionDualSnapshot
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:16:19.16346+00:00
-- url     : https://prove2.me/theorems/ec897548-3376-4f72-8ade-57583a3d7f04
-- title:
--   Weighted blossom matching — the contraction dual snapshot
-- statement:
--   The dual snapshot advances both potentials and the cumulative matching clock while retaining the selected natural-memory layout used to write the contraction record.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionArm

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.MatchingChosenStage.contractionDualSnapshot
    {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)}
    {original s : ArithmeticState} (chosen : MatchingChosenStage part forest positive cutAt original s)
    (search : CompactMatchingSearchForest part forest state.partialMate part.tightBetween)
    (internal : state.InternalCuts) (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (storage : MatchingStageStorage k original s) :
    let bound : DualBound (MatchingDualEvent k) := ⟨chosen.event, s.rr 1⟩
    let nextPart := part.advanceSearch search positive internal bound chosen.adjustment
    ∃ advanced : MatchingAdvancedStage nextPart forest positive cutAt original
        (matchingContractionDualSnapshot s),
      advanced.dual.node = chosen.dual.node ∧ advanced.registry.trees.tree = chosen.registry.trees.tree := by sorry
