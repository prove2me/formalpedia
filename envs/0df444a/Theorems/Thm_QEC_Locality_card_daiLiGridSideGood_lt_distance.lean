-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiGridSideGood_lt_distance
-- name    : QEC.Locality.card_daiLiGridSideGood_lt_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:13:22.547732+00:00
-- url     : https://prove2.me/theorems/a0b3a96f-98a8-4093-ab69-0c95d488c5ef
-- title:
--   Locality: card dai Li Grid Side Good lt distance
-- statement:
--   The same packing estimate holds after removing long-interaction endpoints.
--   The hypotheses state the actual positive dimensions of the side rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1877-L1901
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1877-L1901

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable

theorem QEC.Locality.card_daiLiGridSideGood_lt_distance
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold : ℝ)
    {w ell : ℝ} (origin : ℝ × ℝ) (side : DaiLiGridSideIndex)
    (hEdge : 1 ≤ 2 * ell) (hLong : 1 ≤ w - 4 * ell)
    (hSmall : 12 * ell * (w - 4 * ell) < d) :
    (daiLiGridSideGoodQubits P embedding threshold w ell origin side).card < d := by sorry
