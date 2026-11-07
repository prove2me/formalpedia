-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_cone_slice_iff
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.cone_slice_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:49:48.785479+00:00
-- url     : https://prove2.me/theorems/d16d7cbf-ca8d-4173-9ee4-c52cc77bad6b
-- title:
--   Spherical Cap: cone slice iff
-- statement:
--   The cone inequality is a disk inequality at each fixed axial height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L31-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L31-L51

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.cone_slice_iff {c z q : ℝ} (hc : 0 < c) (hq : 0 ≤ q) :
    c * Real.sqrt (z ^ 2 + q ^ 2) ≤ z ↔
      0 ≤ z ∧ q ^ 2 ≤ coneSlopeSq c * z ^ 2 := by sorry
