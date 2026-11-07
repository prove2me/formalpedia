-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiDGeKExceptional_into_B
-- name    : QEC.Locality.mem_daiLiDGeKExceptional_into_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:36.592757+00:00
-- url     : https://prove2.me/theorems/f66ee412-0080-4a5c-bd46-cf6875128c36
-- title:
--   Locality: mem dai Li DGe KExceptional into B
-- statement:
--   The exceptional component is one of the concrete pieces assembled into
--   the untrimmed Case-2 `B` subsystem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L657-L664
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L657-L664

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

theorem QEC.Locality.mem_daiLiDGeKExceptional_into_B
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (q : ι)
    (hq : q ∈ daiLiDGeKExceptionalBadQubits P embedding threshold w ell t) :
    q ∈ (daiLiDGeKBSubsystem P embedding threshold w ell t).selected := by sorry
