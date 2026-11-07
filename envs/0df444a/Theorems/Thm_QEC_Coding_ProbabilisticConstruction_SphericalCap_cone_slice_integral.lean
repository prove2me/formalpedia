-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_cone_slice_integral
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.cone_slice_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:53:44.831517+00:00
-- url     : https://prove2.me/theorems/c93205f0-186b-4954-a7b9-a17a716ff147
-- title:
--   Spherical Cap: cone slice integral
-- statement:
--   Integrating the two polynomial slices gives the solid-cone volume.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L134-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L134-L146

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.cone_slice_integral {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    (∫ z in (0 : ℝ)..c, Real.pi * (coneSlopeSq c * z ^ 2)) +
      (∫ z in c..1, Real.pi * (1 - z ^ 2)) =
        (2 * Real.pi / 3) * (1 - c) := by sorry
