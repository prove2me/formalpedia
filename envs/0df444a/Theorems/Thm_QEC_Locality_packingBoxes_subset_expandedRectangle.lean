-- Prove2me | Theorems.Thm_QEC_Locality_packingBoxes_subset_expandedRectangle
-- name    : QEC.Locality.packingBoxes_subset_expandedRectangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:01:57.017192+00:00
-- url     : https://prove2.me/theorems/ead51663-681f-4457-ad72-0ca7e66ac47e
-- title:
--   Locality: packing Boxes subset expanded Rectangle
-- statement:
--   The Locality construction uses the packing Boxes subset expanded Rectangle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L645-L657
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L645-L657

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

theorem QEC.Locality.packingBoxes_subset_expandedRectangle
    {i : Type*} [DecidableEq i]
    (embedding : QEC.Locality.UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (⋃ p ∈ s, packingBox (embedding.point p)) ⊆ expandedRectangle lower upper := by sorry
