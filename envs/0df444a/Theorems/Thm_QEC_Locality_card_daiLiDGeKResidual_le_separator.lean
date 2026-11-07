-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiDGeKResidual_le_separator
-- name    : QEC.Locality.card_daiLiDGeKResidual_le_separator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:14:51.489966+00:00
-- url     : https://prove2.me/theorems/bb18ee62-58d7-4be3-a50d-48a0ebb70676
-- title:
--   Locality: card dai Li DGe KResidual le separator
-- statement:
--   The actual residual cardinality is bounded by the computed Case-2
--   separator, with no partition or cut supplied by a caller.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L807-L816
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L807-L816

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

theorem QEC.Locality.card_daiLiDGeKResidual_le_separator
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w)
    (hGlobal : 10 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) < d)
    (hw : 0 < w) (hEll : 0 < ell) :
    (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected.card ≤
      (daiLiDGeKSeparator P embedding threshold w ell t).card := by sorry
