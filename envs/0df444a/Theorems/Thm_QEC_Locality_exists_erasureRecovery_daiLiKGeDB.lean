-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiKGeDB
-- name    : QEC.Locality.exists_erasureRecovery_daiLiKGeDB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:16:58.251917+00:00
-- url     : https://prove2.me/theorems/450ffa70-b508-463b-93b6-3c398cd50eaf
-- title:
--   Locality: exists erasure Recovery dai Li KGe DB
-- statement:
--   The complete finite `k >= d` source-side region `B` has an actual CPTP
--   erasure recovery.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3791-L3840
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3791-L3840

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

theorem QEC.Locality.exists_erasureRecovery_daiLiKGeDB
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
    (hInternalSideScale : 12 * ell * w < d)
    (hEll : 0 < ell) (hGridWidth : 4 * ell ≤ w)
    (hThresholdEll : threshold ≤ ell)
    (hEdge : 1 ≤ 2 * ell) (hGridLong : 1 ≤ w - 4 * ell)
    (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).complementSystem
        P.semanticCode
        (daiLiKGeDBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).erasureChannelFromRegister
        recovery := by sorry
