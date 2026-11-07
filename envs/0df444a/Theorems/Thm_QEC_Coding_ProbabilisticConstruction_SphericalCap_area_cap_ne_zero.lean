-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_ne_zero
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:51:08.31582+00:00
-- url     : https://prove2.me/theorems/893a2b10-4103-40ce-b92a-b0931fc5d76a
-- title:
--   Spherical Cap: area cap ne zero
-- statement:
--   Positivity follows already from a nonempty relatively open subcap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L72-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L72-L83

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_ne_zero (u : Sphere) {c : ℝ} (hc : c < 1) :
    area (cap u c) ≠ 0 := by sorry
