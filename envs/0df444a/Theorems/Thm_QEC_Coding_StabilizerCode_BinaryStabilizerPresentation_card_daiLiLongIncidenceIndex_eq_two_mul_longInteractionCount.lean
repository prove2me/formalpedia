-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_card_daiLiLongIncidenceIndex_eq_two_mul_longInteractionCount
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.card_daiLiLongIncidenceIndex_eq_two_mul_longInteractionCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:02:36.063073+00:00
-- url     : https://prove2.me/theorems/432084f9-a0ec-4364-9a0a-74ec804d7256
-- title:
--   Binary Stabilizer Presentation: card dai Li Long Incidence Index eq two mul long Interaction Count
-- statement:
--   The incidence multiset has exactly twice the distinct unordered long-edge count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L1062-L1068
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L1062-L1068

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Coding QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {i : Type u} [Fintype i] [DecidableEq i]
variable {kappa : Type v} [Fintype kappa]

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.card_daiLiLongIncidenceIndex_eq_two_mul_longInteractionCount
    (P : BinaryStabilizerPresentation (ι := i) (κ := kappa))
    (embedding : Locality.UnitSeparatedEmbedding2D i) (threshold : ℝ) :
    Fintype.card (P.daiLiLongIncidenceIndex embedding threshold) =
      2 * P.longInteractionCount embedding threshold := by sorry
