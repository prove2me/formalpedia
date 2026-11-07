-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_cap
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:51:31.468369+00:00
-- url     : https://prove2.me/theorems/ce08d123-3ab0-4ad6-860c-48626430d356
-- title:
--   Spherical Cap: measurable Set cap
-- statement:
--   The Spherical Cap construction uses the measurable Set cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L68-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L68-L69

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_cap (u : Sphere) (c : ℝ) : MeasurableSet (cap u c) := by sorry
