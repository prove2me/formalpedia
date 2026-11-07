-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiDGeKB
-- name    : QEC.Locality.exists_erasureRecovery_daiLiDGeKB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:14:16.311133+00:00
-- url     : https://prove2.me/theorems/608837c1-961d-4cba-93e0-2a159fcffc4a
-- title:
--   Locality: exists erasure Recovery dai Li DGe KB
-- statement:
--   DL24 Case 2's entire `B` region has an actual CPTP erasure recovery.  The
--   caller supplies only the source's numerical scale checks; its partition,
--   endpoint routing, local recoveries, and pairwise decoupling are constructed
--   above from the finite interaction graph and translated grid.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L548-L597
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L548-L597

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

theorem QEC.Locality.exists_erasureRecovery_daiLiDGeKB
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
        (daiLiDGeKBSubsystem P embedding threshold w ell t).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiDGeKBSubsystem P embedding threshold w ell t).complementSystem
        P.semanticCode
        (daiLiDGeKBSubsystem P embedding threshold w ell t).erasureChannelFromRegister
        recovery := by sorry
