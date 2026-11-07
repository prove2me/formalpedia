-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_volume_disk_sqrt
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.volume_disk_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:53:28.70374+00:00
-- url     : https://prove2.me/theorems/6d01ef6b-8f31-41d8-b724-7e19d3c48a70
-- title:
--   Spherical Cap: volume disk sqrt
-- statement:
--   Exact two-dimensional slice area, including the radius-zero degeneracy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L69-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L69-L76

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.volume_disk_sqrt {a : ℝ} (ha : 0 ≤ a) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt a)) =
      ENNReal.ofReal (Real.pi * a) := by sorry
