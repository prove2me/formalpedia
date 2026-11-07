-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiDGeKTrimmedB
-- name    : QEC.Locality.exists_erasureRecovery_daiLiDGeKTrimmedB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:35.018509+00:00
-- url     : https://prove2.me/theorems/8237b596-48c3-4e79-b080-e443545fb1e8
-- title:
--   Locality: exists erasure Recovery dai Li DGe KTrimmed B
-- statement:
--   The second #368 region inherits the actual CPTP recovery of the complete
--   Case-2 `B` construction by selected-subsystem inclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L601-L624
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L601-L624

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK

theorem QEC.Locality.exists_erasureRecovery_daiLiDGeKTrimmedB
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (hEll : 0 < ell) (hWidth : 4 * ell ≤ w)
    (hThresholdEll : threshold ≤ ell)
    (hEdge : 1 ≤ 2 * ell) (hLongStrip : 1 ≤ w - 4 * ell)
    (hSmallStrip : 12 * ell * (w - 4 * ell) < d)
    (hLongCount : 2 * P.longInteractionCount embedding threshold < d) :
    ∃ recovery : QuantumChannel
        (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).complementSystem
        P.semanticCode
        (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).erasureChannelFromRegister
        recovery := by sorry
