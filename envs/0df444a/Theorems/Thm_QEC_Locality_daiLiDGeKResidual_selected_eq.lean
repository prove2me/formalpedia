-- Prove2me | Theorems.Thm_QEC_Locality_daiLiDGeKResidual_selected_eq
-- name    : QEC.Locality.daiLiDGeKResidual_selected_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:14:00.939132+00:00
-- url     : https://prove2.me/theorems/8e22b8d1-4c27-495e-852c-a0544d07fe85
-- title:
--   Locality: dai Li DGe KResidual selected eq
-- statement:
--   Exported definitional identity for the actual Case-2 residual requested by
--   the #368 interface.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L144-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L144-L151

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

theorem QEC.Locality.daiLiDGeKResidual_selected_eq
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) :
    (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected =
      Finset.univ \
        ((daiLiDGeKASubsystem P embedding d threshold w ell t).selected ∪
          (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).selected) := by sorry

attribute [defeq] QEC.Locality.daiLiDGeKResidual_selected_eq
