-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_angle
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_angle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:38:53.581845+00:00
-- url     : https://prove2.me/theorems/5f5978fa-1c59-46c6-b186-7ee772829521
-- title:
--   Spherical Cap: area cap angle
-- statement:
--   The Spherical Cap construction uses the area cap angle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L145-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L145-L147

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_angle (u : Sphere) {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    area (cap u (Real.cos θ)) = ENNReal.ofReal (2*Real.pi*(1-Real.cos θ)) := by sorry
