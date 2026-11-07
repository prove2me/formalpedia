-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiKGeDGoodRegionCore
-- name    : QEC.Locality.exists_erasureRecovery_daiLiKGeDGoodRegionCore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:16:00.174792+00:00
-- url     : https://prove2.me/theorems/cfa9631b-4848-4b17-a098-1beb57381521
-- title:
--   Locality: exists erasure Recovery dai Li KGe DGood Region Core
-- statement:
--   A good-cell member of the finite `k >= d` family has an actual CPTP
--   recovery.  The source-good classification is recovered from the candidate
--   index itself, and the strict core inherits the closed-cell recovery by subset
--   closure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2623-L2692
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2623-L2692

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

theorem QEC.Locality.exists_erasureRecovery_daiLiKGeDGoodRegionCore
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ)
    (hCandidate : Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVertical : baseVerticalRadius ≤ w / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVertical : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hBaseCard : (centeredRectangleQubits embedding
      (daiLiGridCellCenter w (gridOrigin w t) cell)
      baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inl cell)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inl cell)).complementSystem
        P.semanticCode
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inl cell)).erasureChannelFromRegister recovery := by sorry
