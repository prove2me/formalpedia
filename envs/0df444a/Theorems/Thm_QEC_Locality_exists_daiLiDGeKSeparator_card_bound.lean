-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiDGeKSeparator_card_bound
-- name    : QEC.Locality.exists_daiLiDGeKSeparator_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:14:52.87627+00:00
-- url     : https://prove2.me/theorems/54e0ea25-e62a-4eef-b0e4-587282461842
-- title:
--   Locality: exists dai Li DGe KSeparator card bound
-- statement:
--   One translated grid simultaneously controls the concrete Case-2 separator.
--   The `64` is the formalization's explicit two-endpoint charge: #385 bounds
--   directed edge incidences by `32 * ell / w * N`, and `C` keeps both endpoints.
--   Here `N` is still the cardinality of distinct unordered long interactions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L997-L1019
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L997-L1019

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

theorem QEC.Locality.exists_daiLiDGeKSeparator_card_bound
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (hEll : 0 < ell) (hScale : 4 * ell ≤ w) :
    ∃ t : GridTranslation w,
      ((daiLiDGeKSeparator P embedding threshold w ell t).card : ℝ) ≤
        (32 * ell ^ 2 / w ^ 2) * Fintype.card ι +
          64 * ell / w * (P.longInteractionCount embedding threshold : ℝ) := by sorry
