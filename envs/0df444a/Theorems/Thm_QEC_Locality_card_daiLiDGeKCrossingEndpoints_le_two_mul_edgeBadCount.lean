-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiDGeKCrossingEndpoints_le_two_mul_edgeBadCount
-- name    : QEC.Locality.card_daiLiDGeKCrossingEndpoints_le_two_mul_edgeBadCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:28.17217+00:00
-- url     : https://prove2.me/theorems/6a0b0c01-6a72-4650-b199-e585468bb20c
-- title:
--   Locality: card dai Li DGe KCrossing Endpoints le two mul edge Bad Count
-- statement:
--   The crossing endpoint set costs at most twice the selected long-incidence
--   count: once for the B' endpoint and once for its opposite endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L265-L289
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L265-L289

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

theorem QEC.Locality.card_daiLiDGeKCrossingEndpoints_le_two_mul_edgeBadCount
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) :
    (daiLiDGeKCrossingEndpoints P embedding threshold w ell t).card ≤
      2 * edgeBadCount w (2 * ell)
        (P.daiLiLongIncidencePoint embedding threshold) t := by sorry
