-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capLaw_angle_isProbabilityMeasure
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.capLaw_angle_isProbabilityMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:38:53.058504+00:00
-- url     : https://prove2.me/theorems/16b05d7c-abb0-4d86-a207-4b9dc24353b5
-- title:
--   Spherical Cap: cap Law angle is Probability Measure
-- statement:
--   The Spherical Cap construction uses the cap Law angle is Probability Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L149-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L149-L151

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.capLaw_angle_isProbabilityMeasure (u : Sphere) {θ : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) : IsProbabilityMeasure (capLaw u (Real.cos θ)) := by sorry
