-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialCone_section
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.axialCone_section
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:53:36.239426+00:00
-- url     : https://prove2.me/theorems/b6936a03-8e6c-48c1-bbb4-8122433add6c
-- title:
--   Spherical Cap: axial Cone section
-- statement:
--   The two constraints on the transverse disk are simultaneously exact.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L88-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L88-L114

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.axialCone_section {c z : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    {y : Transverse | axialEquiv.symm (z, y) ∈ axialCone c} =
      closedBall 0 (Real.sqrt (min (coneSlopeSq c * z ^ 2) (1 - z ^ 2))) := by sorry
