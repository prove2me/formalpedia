-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:08:10.61625+00:00
-- url     : https://prove2.me/theorems/bf018d0b-f339-44b0-a8d9-5f7097dbf4a8
-- title:
--   Spherical Cap: area cap
-- statement:
--   Exact surface area of a closed spherical cap, for the entire cutoff interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L116-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L116-L137

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap (u : Sphere) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) :
    area (cap u c) = ENNReal.ofReal (2 * Real.pi * (1-c)) := by sorry
