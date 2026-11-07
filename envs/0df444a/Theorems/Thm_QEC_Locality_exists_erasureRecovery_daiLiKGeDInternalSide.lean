-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiKGeDInternalSide
-- name    : QEC.Locality.exists_erasureRecovery_daiLiKGeDInternalSide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:16:16.664314+00:00
-- url     : https://prove2.me/theorems/eab780b2-9fea-4e90-a05d-1933e16a976e
-- title:
--   Locality: exists erasure Recovery dai Li KGe DInternal Side
-- statement:
--   A canonical internal bad-rectangle side has a direct CPTP recovery through
--   the local box-scale packing proof, then subset closure after the separator is
--   removed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3056-L3118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3056-L3118

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

theorem QEC.Locality.exists_erasureRecovery_daiLiKGeDInternalSide
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
    (hEllNat : 1 ≤ ell) (hCellWidth : 5 * ell ≤ w)
    (hSideScale : 12 * ell * w < d)
    (side : DaiLiKGeDInternalSideIndex)
    (hCandidate : side ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDInternalSideSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles side).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDInternalSideSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles side).complementSystem
        P.semanticCode
        (daiLiKGeDInternalSideSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles side).erasureChannelFromRegister
        recovery := by sorry
