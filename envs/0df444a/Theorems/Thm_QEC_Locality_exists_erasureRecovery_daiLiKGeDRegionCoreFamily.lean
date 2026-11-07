-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiKGeDRegionCoreFamily
-- name    : QEC.Locality.exists_erasureRecovery_daiLiKGeDRegionCoreFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:16:22.077218+00:00
-- url     : https://prove2.me/theorems/84217555-81aa-4da0-8d91-f6927d56de20
-- title:
--   Locality: exists erasure Recovery dai Li KGe DRegion Core Family
-- statement:
--   The finite union of all source-region cores has an actual CPTP erasure
--   recovery.  Each branch is discharged by its local construction, and the
--   family closure receives the proved geometric decoupling above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2879-L2964
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2879-L2964

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable

theorem QEC.Locality.exists_erasureRecovery_daiLiKGeDRegionCoreFamily
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hThreshold : 1 ≤ threshold) (hWidthNat : 1 ≤ w) (hEllNat : 1 ≤ ell)
    (hEll : 0 < ell) (hWidth : 0 < w) (hThresholdEll : threshold ≤ ell)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hGoodBaseCard : ∀ cell,
      Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d
        w (gridOrigin w t) rectangles →
      (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
        baseHorizontalRadius baseVerticalRadius).card < d)
    (hBadBaseCard : ∀ cell slot,
      Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding threshold d
        w (gridOrigin w t) rectangles →
      (centeredRectangleQubits embedding
        (daiLiRectangleCenter
          (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
            (Sum.inr (cell, slot))).1
          (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
            (Sum.inr (cell, slot))).2)
        baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem
          (daiLiKGeDRegionCoreFamily P embedding threshold w ell t
            (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
          (daiLiKGeDRegionCandidates P embedding threshold d w (gridOrigin w t) rectangles)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem
          (daiLiKGeDRegionCoreFamily P embedding threshold w ell t
            (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
          (daiLiKGeDRegionCandidates P embedding threshold d w (gridOrigin w t) rectangles)).complementSystem
        P.semanticCode
        (familyUnionSubsystem
          (daiLiKGeDRegionCoreFamily P embedding threshold w ell t
            (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
          (daiLiKGeDRegionCandidates P embedding threshold d w (gridOrigin w t) rectangles)).erasureChannelFromRegister
        recovery := by sorry
