-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiKGeDBadRegionCore
-- name    : QEC.Locality.exists_erasureRecovery_daiLiKGeDBadRegionCore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:16:11.267839+00:00
-- url     : https://prove2.me/theorems/8a776c73-6ae7-4065-aed3-b4dc71af75cd
-- title:
--   Locality: exists erasure Recovery dai Li KGe DBad Region Core
-- statement:
--   A bad-rectangle member of the finite `k >= d` family has an actual CPTP
--   recovery.  Its source is the in-range #496 list entry, whose proved
--   low-counter/short-height alternative selects the growth or packing route.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2697-L2817
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2697-L2817

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

theorem QEC.Locality.exists_erasureRecovery_daiLiKGeDBadRegionCore
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
    (cell : ℤ × ℤ) (slot : ℕ)
    (hCandidate : Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold) (hWidth : 1 ≤ w) (hEll : 1 ≤ ell)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVertical : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVertical : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hBaseCard : (centeredRectangleQubits embedding
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
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inr (cell, slot))).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inr (cell, slot))).complementSystem
        P.semanticCode
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inr (cell, slot))).erasureChannelFromRegister recovery := by sorry
