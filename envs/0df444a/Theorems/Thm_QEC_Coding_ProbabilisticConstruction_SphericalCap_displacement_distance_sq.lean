-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacement_distance_sq
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.displacement_distance_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:04:41.496015+00:00
-- url     : https://prove2.me/theorems/47f02cfe-51f2-4c96-9d0d-bf2c83bc1dc9
-- title:
--   Spherical Cap: displacement distance sq
-- statement:
--   The Spherical Cap construction uses the displacement distance sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/SmallCap.lean#L7-L13
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/SmallCap.lean#L7-L13

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_SmallCap
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set Metric
open scoped ENNReal

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.displacement_distance_sq (R : ℝ) (s v : Sphere) :
    dist (R • (s : Space)) (R • (v : Space)) ^ 2 =
      2 * R^2 * (1 - inner ℝ (v : Space) (s : Space)) := by sorry
