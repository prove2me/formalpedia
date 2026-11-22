-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_matchingAugmentationHandlerBlock_selectedLift
-- name    : VehicleRoutingSurvey.Routing.matchingAugmentationHandlerBlock_selectedLift
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:01:35.351534+00:00
-- url     : https://prove2.me/theorems/2d5f14d2-ad9b-4460-a33d-feac2c98981e
-- title:
--   Weighted blossom matching — lifting the augmenting path
-- statement:
--   The selected augmenting path lifts through the stored blossoms to an original-vertex matching and produces the specified RAM output.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.matchingAugmentationHandlerBlock_selectedLift {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {caller initial s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest (matchingAugmentDualPoint s)}
    {registry : MatchingRegistryView dual} (cycles : MatchingLiveCycles registry)
    (top : CompactTopMatching part) (allCuts : old.InternalCuts)
    (valid : forest.valid old.partialMate part.tightBetween)
    (links : MatchingForestLinkMemory part forest (matchingAugmentDualPoint s))
    (stored : MatchingForestOriginalWitnesses part forest (matchingAugmentDualPoint s))
    (primal : CompactMatchingPrimalDualMemory old caller s)
    (storage : MatchingStageStorage k caller s) (order : MatchingCycleRecordOrder s)
    (capacity : ∀ n < s.nr 76, n < matchingBlossomCapacity k)
    (trigger : Fin k × Fin k) {a b : Fin k} {pa pb : Option (Fin k)} {traceBase : ℕ}
    (aOuter : forest.role a = .outer pa) (bOuter : forest.role b = .outer pb)
    (different : forest.commonAncestor a b = none)
    (direction : (part.representative trigger.1,part.representative trigger.2) = (a,b))
    (triggerTight : matchingLiftTight old s(trigger.1,trigger.2))
    (traced : MatchingForestTraceResult forest a b traceBase initial s)
    (triggerRAM : (s.nr 92,s.nr 93) = (trigger.1.val,trigger.2.val))
    (entry : s.pc = 0) (live : s.halted = false) (one : s.nr 9 = 1) :
    let witness := matchingAugmentationSavedWitness stored
    let rows := forestAugmentationCrossings witness trigger (forest.traceToRoot a) (forest.traceToRoot b)
    ∃ (next : CompactMatchingPrimalDual k cost) (nextPart : CompactMatchingPartition next)
      (t : ArithmeticState) (steps : ℕ),
      BlockRuns matchingAugmentationHandlerBlock steps s t ∧ t.halted = false ∧
      steps + (34*k+61) ≤ 512*(k^2+1) ∧
      t.nr 1 = 0 ∧ t.nr 33 = 0 ∧ t.nr 82 = 0 ∧
      t.rr 15 = s.rr 15+s.rr 1 ∧ t.rm = iterateBlossomDuals {s with rm := advancedEffectiveMemory s} k ∧
      CompactMatchingPrimalDualMemory next caller t ∧ next.edges.card = old.edges.card+1 ∧
      next.InternalCuts ∧ CompactTopMatching nextPart ∧ nextPart.blocks.block = part.blocks.block ∧
      next.cuts = old.cuts ∧ next.potential = old.potential ∧ next.cutDual = old.cutDual ∧
      ∃ (base : ArithmeticState) (jobs : List MatchingRebaseTask) (prepared : MatchingPreparedLift base jobs (compactPrimalMateWord next)),
        MatchingAugmentPreparedRegistry cycles rows nextPart prepared ∧
        MatchingRebaseCompletedRows prepared.lift jobs t := by sorry
