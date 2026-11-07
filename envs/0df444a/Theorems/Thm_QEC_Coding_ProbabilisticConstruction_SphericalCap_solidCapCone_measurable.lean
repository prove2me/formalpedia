-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_solidCapCone_measurable
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.solidCapCone_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:55:33.052591+00:00
-- url     : https://prove2.me/theorems/e0ea1c02-741d-41d2-8ea5-443a94604f8c
-- title:
--   Spherical Cap: solid Cap Cone measurable
-- statement:
--   The Spherical Cap construction uses the solid Cap Cone measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeBridge.lean#L10-L15
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeBridge.lean#L10-L15

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.solidCapCone_measurable (u : Sphere) (c : ℝ) :
    MeasurableSet (solidCapCone u c) := by sorry
