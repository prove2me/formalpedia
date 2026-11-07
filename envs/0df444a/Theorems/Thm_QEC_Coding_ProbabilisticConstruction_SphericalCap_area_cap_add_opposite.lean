-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_add_opposite
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_add_opposite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:10:23.067551+00:00
-- url     : https://prove2.me/theorems/13c6e45b-4eec-4ab0-b9ef-cd20d067549d
-- title:
--   Spherical Cap: area cap add opposite
-- statement:
--   The Spherical Cap construction uses the area cap add opposite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L108-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L108-L113

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_add_opposite (u : Sphere) (c : ℝ) :
    area (cap u c) + area (cap (opposite u) (-c)) = ENNReal.ofReal (4 * Real.pi) := by sorry
