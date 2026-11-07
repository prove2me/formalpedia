-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_coneSlopeSq_mul_le_ball
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.coneSlopeSq_mul_le_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:53:35.428202+00:00
-- url     : https://prove2.me/theorems/b525a7fb-c94e-416e-b702-a10babe7f088
-- title:
--   Spherical Cap: cone Slope Sq mul le ball
-- statement:
--   The cone is the active radial constraint below the cutoff height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L54-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeSlices.lean#L54-L59

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.coneSlopeSq_mul_le_ball {c z : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hz0 : 0 ≤ z) (hzc : z ≤ c) :
    coneSlopeSq c * z ^ 2 ≤ 1 - z ^ 2 := by sorry
