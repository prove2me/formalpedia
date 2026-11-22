-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_matchingContractionRegistersCycles
-- name    : VehicleRoutingSurvey.Routing.matchingContractionRegistersCycles
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T16:16:45.873053+00:00
-- url     : https://prove2.me/theorems/633b1713-b922-47a3-8e5f-c4e737b255cc
-- title:
--   Weighted blossom matching — contraction registry and live cycles
-- statement:
--   Registering the newly contracted odd cycle preserves the typed live-cycle archive and gives the registry view for the next selector state.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionArm

open VehicleRoutingSurvey.Routing SupplyChainTheory

theorem VehicleRoutingSurvey.Routing.matchingContractionRegistersCycles {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {part : CompactMatchingPartition state} {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (live : MatchingLiveCycles registry) (top : CompactTopMatching part) (left right : List (Fin k)) (base : Fin k)
    (unique : (contractionCycleOrder left right base).Nodup) (odd : Odd (contractionCycleOrder left right base).length)
    (many : 1 < (contractionCycleOrder left right base).length)
    (fixed : ∀ p ∈ (contractionCycleOrder left right base).toFinset, part.representative p = p)
    (mate : ∀ x ∈ (contractionCycleOrder left right base).toFinset, x ≠ base →
      ∃ y ∈ (contractionCycleOrder left right base).toFinset, y ≠ base ∧ state.partialMate x = some y)
    (pairs : ∀ x y, s(x,y) ∈ alternatingEdges (right.reverse ++ left) → state.partialMate x = some y ∧ state.partialMate y = some x)
    (rows : let cycle := contractionCycleOrder left right base
      ∀ i : Fin cycle.length, let row := matchingContractionWrittenChild s i.val
        let p := cycle.get i
        let q := cycle.get ⟨(i.val+1)%cycle.length,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
        row.representative = p.val ∧ row.node = (matchingCycleRecordReference s).nm (s.nr 74+p.val) ∧
          ContractionCycleEdgeWords part p q (row.endpointA,row.endpointB))
    (oldPtrs : ∀ p : Fin k, (matchingCycleRecordReference s).nm (s.nr 74+p.val) = blossomNodeAt s p.val)
    (order : MatchingCycleRecordOrder s) (ports : ∀ r ∈ ([55,65,77,78,79,80] : List ℕ), t.nr r = s.nr r)
    (held : ∀ a, matchingContractionOldArchive s a → t.nm a = s.nm a)
    (topNodes : ∀ p : Fin k, blossomNodeAt t p.val =
      if p = base then s.nr 76 else if p ∈ (contractionCycleOrder left right base).toFinset then 0 else blossomNodeAt s p.val)
    (count : t.nm (t.nr 78+s.nr 76) = (contractionCycleOrder left right base).length)
    (table : ∀ i < (contractionCycleOrder left right base).length, matchingCycleChildAt t.nm (matchingCycleRecordStart t (s.nr 76)+4*i) =
      matchingContractionWrittenChild s i)
    (newCursor : t.nr 76 = s.nr 76+1) (startSafe : t.nr 77+s.nr 76 < t.nr 79) (countSafe : t.nr 78+s.nr 76 < t.nr 79)
    (past : matchingRebaseScratchEnd t ≤ matchingCycleRecordStart t (s.nr 76)) (separated : t.nr 79+t.nr 55 ≤ t.nr 80)
    (starts : t.nr 65+2*(k*k) ≤ t.nr 77) (counts : t.nr 65+2*(k*k) ≤ t.nr 78) (stack : t.nr 65+2*(k*k) ≤ t.nr 80+3*t.nr 55) :
    let cycle := contractionCycleOrder left right base
    let B := part.contractCut cycle.toFinset
    let baseIn : base ∈ cycle.toFinset := by simp [cycle,contractionCycleOrder]
    let oddCard : Odd cycle.toFinset.card := by
      change Odd (contractionCycleOrder left right base).toFinset.card
      rw [List.toFinset_card_of_nodup unique]
      exact odd
    let joined := part.contract cycle.toFinset base baseIn fixed oddCard (contractionMates_covered mate)
    ∀ (after : MatchingSearchDualMemory joined (forest.contract cycle.toFinset base) t),
      (∀ C ∈ state.cuts, after.node C = dual.node C) → after.node B = s.nr 76 →
      ∃ newRegistry : MatchingRegistryView after, Nonempty (MatchingLiveCycles newRegistry) := by sorry
