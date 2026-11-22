-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_matchingAugmentationHandlerBlock_primal
-- name    : VehicleRoutingSurvey.Routing.matchingAugmentationHandlerBlock_primal
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:01:43.617581+00:00
-- url     : https://prove2.me/theorems/610d939e-1e0b-4ec9-9424-c597db2c4609
-- title:
--   Weighted blossom matching — augmentation and the primal matching
-- statement:
--   The augmentation handler installs the new primal matching while preserving the properties needed for the subsequent weighted matching stages.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.matchingAugmentationHandlerBlock_primal {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {caller s emitted : ArithmeticState}
    {rows : List (Fin k × Fin k)} {emitSteps : ℕ}
    {observed : ∀ base jobs, MatchingPreparedLift base jobs (compactPrimalMateWord next) → Prop}
    (oldMemory : CompactMatchingPrimalDualMemory old caller s)
    (emit : BlockRuns writeAugmentationCrossingsBlock emitSteps s emitted)
    (emittedLive : emitted.halted = false) (emittedRows : AugmentationCrossingsReady rows s emitted)
    (emitBound : emitSteps ≤ 17 * k + 21) (one : s.nr 9 = 1)
    (rolesBelow : s.nr 51 + k ≤ s.nr 86) (repsBelow : s.nr 57 + k ≤ s.nr 86)
    (nodesBelow : s.nr 74 + k ≤ s.nr 86) (originalMap : ∀ i < k, s.nm (s.nr 57 + i) < k)
    (layout : AugmentationInstallLayout k (augmentationCrossingSeed s k))
    (effective : caller.nr 64 ≤ s.nr 62) (blossom : caller.nr 64 ≤ s.nr 75)
    (initial : ∀ dual ticks base, BlockRuns prepareMatchingAugmentationBlock ticks s dual →
      AugmentationPreRebaseReady rows {dual with pc := 0} base →
      ∃ (jobs : List MatchingRebaseTask) (lift : MatchingPreparedLift base jobs (compactPrimalMateWord next)),
        observed base jobs lift ∧ matchingRebaseQueueWork jobs ≤ k) :
    ∃ t steps, BlockRuns matchingAugmentationHandlerBlock steps s t ∧ t.halted = false ∧
      steps + (34 * k + 61) ≤ 512 * (k ^ 2 + 1) ∧ t.nr 1 = 0 ∧ t.nr 33 = 0 ∧ t.nr 82 = 0 ∧
      t.rr 15 = s.rr 15 + s.rr 1 ∧ t.rm = iterateBlossomDuals {s with rm := advancedEffectiveMemory s} k ∧
      CompactMatchingPrimalDualMemory next caller t ∧
      ∃ (base : ArithmeticState) (jobs : List MatchingRebaseTask) (lift : MatchingPreparedLift base jobs (compactPrimalMateWord next)),
        observed base jobs lift ∧ MatchingRebaseCompletedRows lift.lift jobs t := by sorry
