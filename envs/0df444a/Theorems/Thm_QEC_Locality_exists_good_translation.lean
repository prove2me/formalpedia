-- Prove2me | Theorems.Thm_QEC_Locality_exists_good_translation
-- name    : QEC.Locality.exists_good_translation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:01:47.11717+00:00
-- url     : https://prove2.me/theorems/f060ed5e-b2fb-4d46-942a-0ec46c27a365
-- title:
--   Locality: exists good translation
-- statement:
--   The Dai--Li translated-grid lemma for two finite multisets.  The finite index
--   types carry multiplicity, and the same translation simultaneously satisfies
--   the vertex and edge bounds.  The constants `32` and `16` are obtained by
--   doubling the per-point Haar averages `16` and `8`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L530-L552
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L530-L552

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

theorem QEC.Locality.exists_good_translation
    {a b : Type*} [Fintype a] [Fintype b]
    (w ell : ℝ) (hell : 0 < ell) (hscale : 4 * ell ≤ w)
    (X : a → ℝ × ℝ) (Y : b → ℝ × ℝ) :
    ∃ t : AddCircle w × AddCircle w,
      (vertexBadCount w (2 * ell) X t : ℝ) ≤
          (32 * ell ^ 2 / w ^ 2) * Fintype.card a ∧
        (edgeBadCount w (2 * ell) Y t : ℝ) ≤
          (16 * ell / w) * Fintype.card b := by sorry
