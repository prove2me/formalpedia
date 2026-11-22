-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingExpansionChildPorts_searchRows
-- name    : VehicleRoutingSurvey.Routing.MatchingExpansionChildPorts.searchRows
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:00:41.240305+00:00
-- url     : https://prove2.me/theorems/ec95280a-6cd1-4d55-a2e8-ab7950824dcd
-- title:
--   Weighted blossom matching — expansion search tables
-- statement:
--   The search rows after blossom expansion have the meanings and memory representation required by the restored child ports.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.MatchingExpansionChildPorts.searchRows {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {B : Finset (Fin k)}
    (ports : MatchingExpansionChildPorts state B) {forest : AlternatingForestState (Fin k)}
    {positive : 0 < k} {chosen s : ArithmeticState} (event : MatchingSelectedExpansion part forest positive chosen B)
    (zero : state.cutDual B = 0) (internal : state.InternalCuts)
    (external : ∀ p ∈ ports.ports, ∀ w, state.partialMate p = some w → w ∉ ports.block p)
    (children : List (Fin k)) (entry : ℕ) (cycle : ports.ports = (event.base :: children).toFinset)
    (oldLinks : ∀ v, part.representative v ≠ v → forest.role v = .unlabelled)
    (owners : ∀ v : Fin k, expansionChildOf s v.val = if v ∈ B then (ports.owner v).val else k)
    (symmetric : ∀ u v, cost u v = cost v u)
    (nested : ∀ C ∈ state.cuts, ∀ u ∈ C, ∀ v ∈ C, part.blocks.block u = part.blocks.block v)
    (descend : ∀ C ∈ state.cuts.erase B, C ⊆ B → ∃ p ∈ ports.ports, C ⊆ ports.block p)
    (pc : s.pc = 0) (running : s.halted = false) (work : ExpansionCacheFrame s)
    (above : s.nr 65+2*(k*k) ≤ s.nr 88) (nodeBefore : s.nr 74+k ≤ s.nr 88) (space : ExpansionCutReadLayout k s)
    (priorValid : ∀ i < s.nr 61, MatchingCandidateRowValid (matchingTopCutAt part) s i)
    (prior : ∀ group : MatchingCandidateGroup k, LeastSlackEntry ((matchingSearchSlacks part forest positive).filter fun d =>
      @decide _ (Classical.propDecidable (group.admits part.blocks forest (part.representativeOf positive) d)))
      (readMatchingCandidate (matchingTopCutAt part) s group.slot))
    (priorPairs : MatchingSearchOuterBuckets s part.representative (fun v => alternatingRoleCode (forest.role v)) cost
      (effectiveVertexPotential state.cuts state.potential state.cutDual)) :
    let next := state.eraseZeroCut event.present zero
    let opened := part.openZeroCut event.top event.present zero (ports.toExpansionChildren internal external)
    let after := forest.expandBlossom event.parent event.base children entry
    let role := fun v => alternatingRoleCode (after.role v)
    let eff := effectiveVertexPotential next.cuts next.potential next.cutDual
    ∀ (dual : MatchingSearchDualMemory opened after s) (input : MatchingRefreshInput s opened.representative role cost eff),
      ∃ t ticks, BlockRuns restoreExpansionCacheBlock ticks s t ∧ t.halted = false ∧
        ticks ≤ 63*k+(98*k+9)*(matchingExpansionFreshSources k s).length+14 ∧ ExpansionCacheRestored s t ∧
        MatchingSearchRows opened after positive (matchingTopCutAt opened) t ∧
        MatchingSearchOuterBuckets t opened.representative role cost eff ∧ MatchingRefreshInput t opened.representative role cost eff := by sorry
