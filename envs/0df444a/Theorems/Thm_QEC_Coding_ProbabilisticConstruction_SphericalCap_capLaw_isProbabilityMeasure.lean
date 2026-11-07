-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capLaw_isProbabilityMeasure
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.capLaw_isProbabilityMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:51:15.995614+00:00
-- url     : https://prove2.me/theorems/1cd40f91-57a4-4013-830d-468be39ad7b9
-- title:
--   Spherical Cap: cap Law is Probability Measure
-- statement:
--   The Spherical Cap construction uses the cap Law is Probability Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L92-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L92-L97

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.capLaw_isProbabilityMeasure (u : Sphere) {c : ℝ} (hc : c < 1) :
    IsProbabilityMeasure (capLaw u c) := by sorry
