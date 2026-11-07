-- Prove2me | Theorems.Thm_QEC_Locality_daiLiKGeD_lowScale_fourthRoot_longInteractionCount
-- name    : QEC.Locality.daiLiKGeD_lowScale_fourthRoot_longInteractionCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:29.351207+00:00
-- url     : https://prove2.me/theorems/1066d309-fdfc-4495-a14a-ee0b5e71026b
-- title:
--   Locality: dai Li KGe D low Scale fourth Root long Interaction Count
-- statement:
--   The actual low-scale `k >= d` fourth-root count branch.  The theorem
--   chooses the finite averaged grid translation, constructs the #496 rectangles,
--   then invokes #386's CPTP partition theorem and its concrete separator bound.
--   It counts the selected presentation's distinct unordered interactions exactly
--   once through `longInteractionCount`; the doubled incidence total appears only
--   as a derived internal bridge.  The hypotheses following the source scale are
--   the explicit finite recovery-side inequalities still required by #386, not a
--   supplied partition, separator, recovery, or interaction-count conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CountComposition.lean#L151-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CountComposition.lean#L151-L290

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.daiLiKGeD_lowScale_fourthRoot_longInteractionCount
    (P : Coding.StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : Coding.StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell w : ℝ)
    (hScale : ell = daiLiKGeDFourthRootThreshold
      (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ))
    (hWidth : w = daiLiKGeDGridWidth (d : ℝ) ell)
    (hD : 0 < d) (hKGeD : d ≤ P.encodedQubits)
    (hLowScale : (d : ℝ) ≤ Real.sqrt ((P.encodedQubits : ℝ) * Fintype.card ι))
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
    (hGoodBaseCard : ∀ (t : GridTranslation w)
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
    (hBadBaseCard : ∀ (t : GridTranslation w)
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
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + ell) * ell + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d)
    (hCellWidth : 5 * ell ≤ w) (hInternalSideScale : 12 * ell * w < d)
    (hGridWidth : 4 * ell ≤ w) (hGridLong : 1 ≤ w - 4 * ell)
    (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    (P.encodedQubits : ℝ) / 100 ≤ (P.longInteractionCount embedding ell : ℝ) := by sorry
