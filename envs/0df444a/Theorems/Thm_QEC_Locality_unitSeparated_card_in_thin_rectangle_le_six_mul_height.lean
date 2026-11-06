-- Prove2me | Theorems.Thm_QEC_Locality_unitSeparated_card_in_thin_rectangle_le_six_mul_height
-- name    : QEC.Locality.unitSeparated_card_in_thin_rectangle_le_six_mul_height
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:38:57.603618+00:00
-- url     : https://prove2.me/theorems/143185e2-afee-4812-8660-067af97be057
-- title:
--   Locality: unit Separated card in thin rectangle le six mul height
-- statement:
--   A relaxed corollary of the exact factor-four vertical thin-strip bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L955-L965
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L955-L965

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

theorem QEC.Locality.unitSeparated_card_in_thin_rectangle_le_six_mul_height
    {i : Type*} [DecidableEq i]
    (embedding : UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlong : 1 ≤ upper.2 - lower.2)
    (hthin0 : 0 ≤ upper.1 - lower.1) (hthin1 : upper.1 - lower.1 < 1)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 6 * (upper.2 - lower.2) := by sorry
