-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiKGeDInternalSideFamily
-- name    : QEC.Locality.exists_erasureRecovery_daiLiKGeDInternalSideFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:17:13.784885+00:00
-- url     : https://prove2.me/theorems/d1552cf2-832b-401d-8cf9-8fbf755e5f5e
-- title:
--   Locality: exists erasure Recovery dai Li KGe DInternal Side Family
-- statement:
--   The finite union of canonical internal bad-rectangle sides has an actual
--   CPTP erasure recovery.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3501-L3547
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3501-L3547

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

theorem QEC.Locality.exists_erasureRecovery_daiLiKGeDInternalSideFamily
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
    (hEll : 0 < ell) (hWidth : 0 < w) (hThresholdEll : threshold ≤ ell) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem
          (daiLiKGeDInternalSideFamily P embedding threshold w ell t
            (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
          (daiLiKGeDInternalSideCandidates P embedding threshold d w (gridOrigin w t) rectangles)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem
          (daiLiKGeDInternalSideFamily P embedding threshold w ell t
            (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
          (daiLiKGeDInternalSideCandidates P embedding threshold d w (gridOrigin w t) rectangles)).complementSystem
        P.semanticCode
        (familyUnionSubsystem
          (daiLiKGeDInternalSideFamily P embedding threshold w ell t
            (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
          (daiLiKGeDInternalSideCandidates P embedding threshold d w (gridOrigin w t) rectangles)).erasureChannelFromRegister
        recovery := by sorry
