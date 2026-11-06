-- Prove2me | Theorems.Thm_QEC_Locality_unitSeparated_card_in_rectangle_le_six_mul_area
-- name    : QEC.Locality.unitSeparated_card_in_rectangle_le_six_mul_area
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:02:18.102592+00:00
-- url     : https://prove2.me/theorems/9f4bba0b-6296-46b7-8fa8-f7e60cac4129
-- title:
--   Locality: unit Separated card in rectangle le six mul area
-- statement:
--   The source-scale packing bound for rectangles whose two sides are at least one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L754-L764
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L754-L764

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable

theorem QEC.Locality.unitSeparated_card_in_rectangle_le_six_mul_area
    {i : Type*} [DecidableEq i]
    (embedding : QEC.Locality.UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hwidth : 1 ≤ upper.1 - lower.1) (hheight : 1 ≤ upper.2 - lower.2)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 6 * ((upper.1 - lower.1) * (upper.2 - lower.2)) := by sorry
