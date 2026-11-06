-- Prove2me | Theorems.Thm_QEC_Locality_addCircle_dist_le_abs_sub
-- name    : QEC.Locality.addCircle_dist_le_abs_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:34:37.84447+00:00
-- url     : https://prove2.me/theorems/5f4fd556-6155-40de-9534-4e131bc505de
-- title:
--   Locality: add Circle dist le abs sub
-- statement:
--   The quotient-circle metric is no larger than the ordinary coordinate
--   distance to any chosen representative of a grid line.  This is the bridge
--   from finite Euclidean strip witnesses back to the translated periodic counts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L55-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L55-L73

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

theorem QEC.Locality.addCircle_dist_le_abs_sub (w a x : ℝ) (hw : 0 < w) :
    dist (a : AddCircle w) (x : AddCircle w) ≤ |x - a| := by sorry
