-- Prove2me | Theorems.Thm_QEC_Locality_unitSeparated_card_in_thin_rectangle_le_four_mul_longSide
-- name    : QEC.Locality.unitSeparated_card_in_thin_rectangle_le_four_mul_longSide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:49:55.229339+00:00
-- url     : https://prove2.me/theorems/a5a907cb-ddbe-4fb4-b68d-8eb00533756b
-- title:
--   Locality: unit Separated card in thin rectangle le four mul long Side
-- statement:
--   The source thin-rectangle constant, proved by a finite binning argument.
--
--   The source's circle-intersection sketch is not used here: at a rectangle corner
--   its claimed `t / 4` lower bound can fail.  Instead, the proof splits the thin
--   coordinate in two.  For long sides below `3 / 2`, the resulting four cells all
--   have diameter below one.  Otherwise, bins of width `3 / 4`, again split in two,
--   inject the point set into `Fin (⌊4s/3⌋₊ + 1) × Bool`; the floor estimate gives
--   the exact factor four without a boundary-error term.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L776-L918
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L776-L918

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

theorem QEC.Locality.unitSeparated_card_in_thin_rectangle_le_four_mul_longSide
    {i : Type*} [DecidableEq i]
    (embedding : UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlong : 1 ≤ upper.1 - lower.1)
    (hthin0 : 0 ≤ upper.2 - lower.2) (hthin1 : upper.2 - lower.2 < 1)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 4 * (upper.1 - lower.1) := by sorry
