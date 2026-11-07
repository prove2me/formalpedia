-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_ball_le_coneSlopeSq_mul
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.ball_le_coneSlopeSq_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:53:33.688226+00:00
-- url     : https://prove2.me/theorems/2db6a1f2-140a-4a5d-90a4-3221532304ba
-- title:
--   Spherical Cap: ball le cone Slope Sq mul
-- statement:
--   The ball is the active radial constraint above the cutoff height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L62-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L62-L66

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.ball_le_coneSlopeSq_mul {c z : ℝ} (hc0 : 0 < c) (hcz : c ≤ z) :
    1 - z ^ 2 ≤ coneSlopeSq c * z ^ 2 := by sorry
