-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiKGeDGridSideUnion
-- name    : QEC.Locality.exists_erasureRecovery_daiLiKGeDGridSideUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:16:54.663652+00:00
-- url     : https://prove2.me/theorems/663fd138-3764-45ab-b7f0-81fc1b119c32
-- title:
--   Locality: exists erasure Recovery dai Li KGe DGrid Side Union
-- statement:
--   The concrete `k >= d` grid-side union inherits an actual CPTP recovery
--   from the established good grid-side family by selected-subsystem closure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3661-L3698
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3661-L3698

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

theorem QEC.Locality.exists_erasureRecovery_daiLiKGeDGridSideUnion
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    {w ell : ℝ} (hEll : 0 < ell) (hWidth : 4 * ell ≤ w)
    (threshold : ℝ) (hThresholdEll : threshold ≤ ell)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hEdge : 1 ≤ 2 * ell) (hLong : 1 ≤ w - 4 * ell)
    (hSideSmall : 12 * ell * (w - 4 * ell) < d) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t cells rectangles).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t cells rectangles).complementSystem
        P.semanticCode
        (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t cells rectangles).erasureChannelFromRegister
        recovery := by sorry
