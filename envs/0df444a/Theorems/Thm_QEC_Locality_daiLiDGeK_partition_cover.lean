-- Prove2me | Theorems.Thm_QEC_Locality_daiLiDGeK_partition_cover
-- name    : QEC.Locality.daiLiDGeK_partition_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:14:32.944288+00:00
-- url     : https://prove2.me/theorems/6b35cdc5-0aee-48d3-adb6-005bf5abb2ce
-- title:
--   Locality: dai Li DGe K partition cover
-- statement:
--   The three concrete Case-2 regions cover every physical qubit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L177-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L177-L195

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

theorem QEC.Locality.daiLiDGeK_partition_cover
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) :
    (daiLiDGeKASubsystem P embedding d threshold w ell t).selected ∪
        (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).selected ∪
          (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected =
      Finset.univ := by sorry
