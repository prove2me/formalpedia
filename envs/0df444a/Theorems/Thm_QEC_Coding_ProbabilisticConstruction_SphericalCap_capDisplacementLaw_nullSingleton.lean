-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capDisplacementLaw_nullSingleton
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_nullSingleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:37:50.218469+00:00
-- url     : https://prove2.me/theorems/629b51e7-272a-4ef0-b931-d7ec7a2b3fbb
-- title:
--   Spherical Cap: cap Displacement Law null Singleton
-- statement:
--   The Spherical Cap construction uses the cap Displacement Law null Singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L127-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L127-L136

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_nullSingleton {R : ℝ} (hR : R ≠ 0) (u : Sphere) (c : ℝ) :
    MeasureTheory.NullSingletonClass (capDisplacementLaw R u c) := by sorry
