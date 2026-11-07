-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiDGeKSeparator_le_badCounts
-- name    : QEC.Locality.card_daiLiDGeKSeparator_le_badCounts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:19:16.204496+00:00
-- url     : https://prove2.me/theorems/ca26f874-8b74-4f78-9c79-0ce03c571d05
-- title:
--   Locality: card dai Li DGe KSeparator le bad Counts
-- statement:
--   The actual Case-2 separator is bounded by the translation's vertex event plus
--   twice its edge-incidence event.  No global ordered-pair or supplied count
--   appears in this statement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L960-L989
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L960-L989

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

theorem QEC.Locality.card_daiLiDGeKSeparator_le_badCounts
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) :
    ((daiLiDGeKSeparator P embedding threshold w ell t).card : ℝ) ≤
      (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        2 * (edgeBadCount w (2 * ell)
          (P.daiLiLongIncidencePoint embedding threshold) t : ℝ) := by sorry
