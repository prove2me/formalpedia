-- Prove2me | Theorems.Thm_QEC_Locality_daiLi_final_interaction_count_max_length_of_geometry
-- name    : QEC.Locality.daiLi_final_interaction_count_max_length_of_geometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:19:39.929876+00:00
-- url     : https://prove2.me/theorems/8582382e-e9fa-4cba-b87b-bc5fc70905c1
-- title:
--   Locality: dai Li final interaction count max length of geometry
-- statement:
--   Conditional Dai--Li branch-composition intermediate.  Its explicit finite
--   recovery-side premises are discharged by the source-assumption bridge below;
--   callers of the final #387 handoff do not receive this interface.  The
--   actual distinct unordered interaction set has at least `max(k,d) / 200`
--   members whose Euclidean length is at least the selected max-form threshold.
--   No partition, recovery, branch result, or interaction count is supplied by
--   the caller.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/FinalComposition.lean#L252-L421
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/FinalComposition.lean#L252-L421

import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Definitions.Def_QEC_Locality_OptimalTradeoff_FinalComposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.daiLi_final_interaction_count_max_length_of_geometry
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell w : ℝ)
    (hScale : ell = daiLiKGeDFourthRootThreshold
      (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ))
    (hWidth : w = daiLiKGeDGridWidth (d : ℝ) ell)
    (hD : 0 < d) (hEncodedPositive : 0 < P.encodedQubits)
    (hAboveBPT : (100 : ℝ) ^ 4 * Fintype.card ι ≤
      (P.encodedQubits : ℝ) * (d : ℝ) ^ 2)
    (hWidthNat : 1 ≤ w)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * ell)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * ell)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * ell)
    (hKGeDGoodBaseCard : ∀ (t : GridTranslation w)
      (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
      (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell)) →
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        rectangles cell = daiLiPhysicalGreedyRectangles P embedding ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell)) →
      ∀ cell,
        Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding ell d w
          (gridOrigin w t) rectangles →
        (centeredRectangleQubits embedding
          (daiLiGridCellCenter w (gridOrigin w t) cell)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hKGeDBadBaseCard : ∀ (t : GridTranslation w)
      (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
      (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell)) →
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        rectangles cell = daiLiPhysicalGreedyRectangles P embedding ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell)) →
      ∀ cell slot,
        Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding ell d w
          (gridOrigin w t) rectangles →
        (centeredRectangleQubits embedding
          (daiLiRectangleCenter
            (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
              (Sum.inr (cell, slot))).1
            (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
              (Sum.inr (cell, slot))).2)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hDGeKGoodBaseCard : ∀ (t : GridTranslation w) cell,
      cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) →
        (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + ell) * ell + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d)
    (hCellWidth : 5 * ell ≤ w) (hInternalSideScale : 12 * ell * w < d)
    (hGridWidth : 4 * ell ≤ w) (hGridLong : 1 ≤ w - 4 * ell)
    (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    max (P.encodedQubits : ℝ) (d : ℝ) / 200 ≤
      (P.longInteractionCount embedding
        (daiLiInteractionCountThreshold (P.encodedQubits : ℝ) d (Fintype.card ι) : ℝ) : ℝ) := by sorry
