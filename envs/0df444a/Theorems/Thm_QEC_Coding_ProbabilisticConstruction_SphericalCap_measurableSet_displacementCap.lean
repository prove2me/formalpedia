-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_displacementCap
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_displacementCap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:51:42.273358+00:00
-- url     : https://prove2.me/theorems/56b8bf78-9ac1-4f1e-b328-9c03a6a6cadb
-- title:
--   Spherical Cap: measurable Set displacement Cap
-- statement:
--   The Spherical Cap construction uses the measurable Set displacement Cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L152-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L152-L156

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_displacementCap (R : ℝ) (u : Sphere) (c : ℝ) :
    MeasurableSet (displacementCap R u c) := by sorry
