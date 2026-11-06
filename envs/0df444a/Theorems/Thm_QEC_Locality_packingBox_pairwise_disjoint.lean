-- Prove2me | Theorems.Thm_QEC_Locality_packingBox_pairwise_disjoint
-- name    : QEC.Locality.packingBox_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:01:46.016721+00:00
-- url     : https://prove2.me/theorems/796edd53-5aac-48ad-a870-ad49e92a273e
-- title:
--   Locality: packing Box pairwise disjoint
-- statement:
--   The Locality construction uses the packing Box pairwise disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L572-L625
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L572-L625

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

theorem QEC.Locality.packingBox_pairwise_disjoint
    {i : Type*} [DecidableEq i]
    (embedding : QEC.Locality.UnitSeparatedEmbedding2D i) (s : Finset i) :
    (s : Set i).PairwiseDisjoint (packingBox ∘ embedding.point) := by sorry
