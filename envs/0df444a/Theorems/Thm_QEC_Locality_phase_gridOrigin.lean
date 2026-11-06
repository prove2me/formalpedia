-- Prove2me | Theorems.Thm_QEC_Locality_phase_gridOrigin
-- name    : QEC.Locality.phase_gridOrigin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:34:22.120127+00:00
-- url     : https://prove2.me/theorems/d4bb8e6f-ca41-4a78-9ddd-978826fa8c6a
-- title:
--   Locality: phase grid Origin
-- statement:
--   The chosen representative realizes the original periodic translation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L48-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L48-L50

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

theorem QEC.Locality.phase_gridOrigin (w : ℝ) (t : GridTranslation w) :
    phase w (gridOrigin w t) = t := by sorry
