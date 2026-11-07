-- Prove2me | Theorems.Thm_QEC_Locality_daiLiDGeKResidual_subset_separator
-- name    : QEC.Locality.daiLiDGeKResidual_subset_separator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:14:42.370722+00:00
-- url     : https://prove2.me/theorems/ce761276-9771-410e-8691-c5328a8764de
-- title:
--   Locality: dai Li DGe KResidual subset separator
-- statement:
--   The actual residual of the Case-2 partition lies in the concrete
--   grid-vertex and bad-interaction-endpoint separator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L780-L803
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L780-L803

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

theorem QEC.Locality.daiLiDGeKResidual_subset_separator
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w)
    (hGlobal : 10 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) < d)
    (hw : 0 < w) (hEll : 0 < ell) :
    (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected ⊆
      daiLiDGeKSeparator P embedding threshold w ell t := by sorry
