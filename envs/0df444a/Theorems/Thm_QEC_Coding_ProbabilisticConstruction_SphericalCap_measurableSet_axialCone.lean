-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_axialCone
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_axialCone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:53:31.464445+00:00
-- url     : https://prove2.me/theorems/dda14e16-ffdd-4519-bd3e-ba91ca2eb0af
-- title:
--   Spherical Cap: measurable Set axial Cone
-- statement:
--   The Spherical Cap construction uses the measurable Set axial Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L82-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L82-L85

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_axialCone (c : ℝ) : MeasurableSet (axialCone c) := by sorry
