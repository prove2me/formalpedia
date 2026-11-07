-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_of_pos
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:08:20.677113+00:00
-- url     : https://prove2.me/theorems/b7e29e12-9b15-458d-8a81-832a9bdcf730
-- title:
--   Spherical Cap: area cap of pos
-- statement:
--   The Spherical Cap construction uses the area cap of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L36-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L36-L43

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_of_pos (u : Sphere) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    area (cap u c) = ENNReal.ofReal (2 * Real.pi * (1-c)) := by sorry
