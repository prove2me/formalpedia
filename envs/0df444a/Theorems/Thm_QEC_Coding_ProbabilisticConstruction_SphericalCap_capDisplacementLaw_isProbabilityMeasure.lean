-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capDisplacementLaw_isProbabilityMeasure
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_isProbabilityMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:08:01.674288+00:00
-- url     : https://prove2.me/theorems/50617882-16d9-4c12-b104-1187cafc7ec4
-- title:
--   Spherical Cap: cap Displacement Law is Probability Measure
-- statement:
--   The Spherical Cap construction uses the cap Displacement Law is Probability Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L108-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L108-L111

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_isProbabilityMeasure (R : ℝ) (u : Sphere) {c : ℝ}
    (hc : c < 1) : IsProbabilityMeasure (capDisplacementLaw R u c) := by sorry
