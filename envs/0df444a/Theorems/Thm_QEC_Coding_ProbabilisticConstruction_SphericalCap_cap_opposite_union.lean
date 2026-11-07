-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_cap_opposite_union
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.cap_opposite_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:08:37.659245+00:00
-- url     : https://prove2.me/theorems/4c60aabc-77ea-480e-8f66-f7d26572da52
-- title:
--   Spherical Cap: cap opposite union
-- statement:
--   The Spherical Cap construction uses the cap opposite union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L89-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L89-L95

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.cap_opposite_union (u : Sphere) (c : ℝ) :
    cap u c ∪ cap (opposite u) (-c) = univ := by sorry
