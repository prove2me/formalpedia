-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiRectangle_of_packing_lt_distance
-- name    : QEC.Locality.exists_erasureRecovery_daiLiRectangle_of_packing_lt_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:15:32.011236+00:00
-- url     : https://prove2.me/theorems/d13012a2-5bf8-46a7-8d49-da8d19285269
-- title:
--   Locality: exists erasure Recovery dai Li Rectangle of packing lt distance
-- statement:
--   A geometrically short #496 rectangle is recovered directly from semantic
--   distance using the exact two-dimensional packing bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2092-L2115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2092-L2115

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

theorem QEC.Locality.exists_erasureRecovery_daiLiRectangle_of_packing_lt_distance
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (lower upper : ℝ × ℝ)
    (hWidth : 1 ≤ upper.1 - lower.1) (hHeight : 1 ≤ upper.2 - lower.2)
    (hPackingSmall : 6 * ((upper.1 - lower.1) * (upper.2 - lower.2)) < d) :
    ∃ recovery : QuantumChannel
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        P.semanticCode
        (daiLiRectangleSubsystem embedding lower upper).erasureChannelFromRegister
          recovery := by sorry
