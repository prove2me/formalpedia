-- Prove2me | Theorems.Thm_QEC_Locality_unitSeparated_card_in_thin_rectangle_le_six_mul_longSide
-- name    : QEC.Locality.unitSeparated_card_in_thin_rectangle_le_six_mul_longSide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:38:36.16257+00:00
-- url     : https://prove2.me/theorems/3bdb3340-f1a6-4521-a2d1-606dddbbffe4
-- title:
--   Locality: unit Separated card in thin rectangle le six mul long Side
-- statement:
--   A relaxed corollary of the exact factor-four horizontal thin-strip bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L942-L952
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L942-L952

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

theorem QEC.Locality.unitSeparated_card_in_thin_rectangle_le_six_mul_longSide
    {i : Type*} [DecidableEq i]
    (embedding : QEC.Locality.UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlong : 1 ≤ upper.1 - lower.1)
    (hthin0 : 0 ≤ upper.2 - lower.2) (hthin1 : upper.2 - lower.2 < 1)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 6 * (upper.1 - lower.1) := by sorry
