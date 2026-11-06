-- Prove2me | Theorems.Thm_QEC_Locality_unitSeparated_card_in_thin_rectangle_le_four_mul_height
-- name    : QEC.Locality.unitSeparated_card_in_thin_rectangle_le_four_mul_height
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:02:26.069461+00:00
-- url     : https://prove2.me/theorems/1c349b38-dd09-404e-b378-1f3ca5122028
-- title:
--   Locality: unit Separated card in thin rectangle le four mul height
-- statement:
--   The exact thin-rectangle source constant with the long side vertical.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L921-L939
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L921-L939

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

theorem QEC.Locality.unitSeparated_card_in_thin_rectangle_le_four_mul_height
    {i : Type*} [DecidableEq i]
    (embedding : UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlong : 1 ≤ upper.2 - lower.2)
    (hthin0 : 0 ≤ upper.1 - lower.1) (hthin1 : upper.1 - lower.1 < 1)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 4 * (upper.2 - lower.2) := by sorry
