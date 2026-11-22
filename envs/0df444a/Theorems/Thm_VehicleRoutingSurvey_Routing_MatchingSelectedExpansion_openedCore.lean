-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingSelectedExpansion_openedCore
-- name    : VehicleRoutingSurvey.Routing.MatchingSelectedExpansion.openedCore
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:01:53.823105+00:00
-- url     : https://prove2.me/theorems/2d06f197-023e-4c77-bbdb-4460f595a4f2
-- title:
--   Weighted blossom matching — opening the selected blossom
-- statement:
--   Opening an eligible blossom exposes its children and reconstructs the mathematical partition, dual state, and local witnesses required by the expansion event.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.MatchingSelectedExpansion.openedCore {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {chosen original s : ArithmeticState}
    {B : Finset (Fin k)} (event : MatchingSelectedExpansion part forest positive chosen B)
    (stage : MatchingAdvancedStage part forest positive (matchingTopCutAt part) original s)
    (live : MatchingLiveCycles stage.registry) (storage : MatchingStageStorage k original s)
    (top : CompactTopMatching part) (internal : state.InternalCuts) (zero : state.cutDual B = 0)
    (selected : s.nr 92 = event.base.val) (pc : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (zeroWord : s.nr 14 = 0) :
    let e := live.entry B event.present
    let g := e.geometry
    let same := (live.selectedBase event).1
    let external := g.exposesPorts top
      (by rw [show e.base = event.base from same]; exact event.active)
      (by rw [show e.base = event.base from same]; exact event.block)
    let opened := part.openZeroCut event.top event.present zero (e.ports.toExpansionChildren internal external)
    let next := state.eraseZeroCut event.present zero
    ∃ (entry : Fin g.cycle.length) (t m a p : ArithmeticState) (ticks : ℕ),
      BlockRuns (appendBlock prepareExpansionChildrenBlock expandMatchingAfterMembersBlock) ticks s t ∧
      t.halted = false ∧ ticks ≤ 207*k+104 ∧ ExpansionMemberMapResult s m e.tree ∧ ExpansionInputLayout k m ∧
      ExpansionArcReady m a entry.val g.baseSlot.val ∧ ExpansionPublication a p ∧
      let after := forest.expandBlossom event.parent e.base g.children (expansionEntryFromBase g.cycle.length entry.val g.baseSlot.val)
      MatchingExpandedForest after next.partialMate (fun _ => True) (matchingExactExpansionEdge next opened.representative)
        opened.representative p t ∧ MatchingExpansionCoreFrame k s t ∧
        ∃ dual : MatchingSearchDualMemory opened after t, dual.node = stage.dual.node := by sorry
