-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_matchingContractionSuffix_searchRows
-- name    : VehicleRoutingSurvey.Routing.matchingContractionSuffix_searchRows
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:00:16.068502+00:00
-- url     : https://prove2.me/theorems/5da26562-8688-4f5d-8610-1a568df8d3c4
-- title:
--   Weighted blossom matching — contraction search tables
-- statement:
--   After the contraction suffix runs, the reconstructed selector rows and search caches describe the new blossom partition.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.matchingContractionSuffix_searchRows {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition state) (forest : AlternatingForestState (Fin k)) (positive : 0 < k)
    (symmetric : ∀ u v, cost u v = cost v u)
    (nested : ∀ S ∈ state.cuts, ∀ u ∈ S, ∀ v ∈ S, part.blocks.block u = part.blocks.block v)
    (cycle : Finset (Fin k)) (base : Fin k) (baseIn : base ∈ cycle) (fixed : ∀ v ∈ cycle, part.representative v = v)
    (odd : Odd cycle.card) (covered : ∀ c ∈ cycle, c ≠ base → c ∈ state.covered) (baseOuter : ∃ p, forest.role base = .outer p)
    (s : ArithmeticState) (absorbed fresh : List (Fin k)) (cutAt : Fin k → Finset (Fin k))
    (entry : s.pc = 0) (live : s.halted = false) (unit : s.nr 9 = 1) (baseAt : s.nr 12 = base.val)
    (absorbedCount : s.nr 87 = absorbed.length) (freshCount : s.nr 99 = fresh.length)
    (absorbedWords : ∀ j : Fin absorbed.length, s.nm (s.nr 86+j.val) = (absorbed.get j).val)
    (freshWords : ∀ j : Fin fresh.length, s.nm (s.nr 88+j.val) = (fresh.get j).val)
    (marked : ∀ v : Fin k, s.nm (s.nr 89+v.val) ≠ 0 ↔ v ∈ cycle)
    (absorbedAfter : s.nr 65+2*(k*k) ≤ s.nr 86) (freshAfter : s.nr 65+2*(k*k) ≤ s.nr 88)
    (markAfter : s.nr 58+s.nr 61 ≤ s.nr 89)
    (valid : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (least : ∀ g, LeastSlackEntry (contractionSearchEntries part forest positive g) (readMatchingCandidate cutAt s g.slot)) :
    let next := part.contract cycle base baseIn fixed odd covered
    let after := forest.contract cycle base
    let oldRole := fun r => alternatingRoleCode (forest.role r)
    let role := fun r => alternatingRoleCode (after.role r)
    let effective := effectiveVertexPotential state.cuts state.potential state.cutDual
    MatchingContractionPairGeometry part.representative next.representative oldRole role base absorbed fresh →
    (∀ v, role (next.representative v) = if v ∈ fresh then 1 else oldRole (part.representative v)) →
    MatchingRefreshInput s next.representative role cost effective →
    MatchingSearchOuterBuckets s part.representative oldRole cost effective →
      ∃ t ticks, ticks ≤ (112+22*absorbed.length)*k + (15+98*k)*fresh.length+16 ∧
        BlockRuns (appendBlock repairMatchingContractionCache resetMatchingSelector) ticks s t ∧ t.halted = false ∧
        t.nr 1 = 0 ∧ MatchingCacheFootprint k s t ∧ t.rr 15 = s.rr 15 ∧
        (∀ r ∉ [0,1,2,3,4,5,6,7,8,10,11,14,15,16,17,18,19,23,24,25,26], t.nr r = s.nr r) ∧
        MatchingSearchRows next after positive cutAt t ∧ MatchingRefreshInput t next.representative role cost effective ∧
        MatchingSearchOuterBuckets t next.representative role cost effective := by sorry
