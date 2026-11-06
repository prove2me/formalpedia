-- Prove2me | Theorems.Thm_QEC_Locality_packing_card_div_two_le_expanded_area
-- name    : QEC.Locality.packing_card_div_two_le_expanded_area
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:04:15.439205+00:00
-- url     : https://prove2.me/theorems/b90a3756-4086-4413-ab24-842ad87db157
-- title:
--   Locality: packing card div two le expanded area
-- statement:
--   The Locality construction uses the packing card div two le expanded area property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L659-L700
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L659-L700

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

theorem QEC.Locality.packing_card_div_two_le_expanded_area
    {i : Type*} [DecidableEq i]
    (embedding : QEC.Locality.UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlx : lower.1 ≤ upper.1) (hly : lower.2 ≤ upper.2)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) / 2 ≤
      (upper.1 - lower.1 + 2 * packingRadius) *
        (upper.2 - lower.2 + 2 * packingRadius) := by sorry
