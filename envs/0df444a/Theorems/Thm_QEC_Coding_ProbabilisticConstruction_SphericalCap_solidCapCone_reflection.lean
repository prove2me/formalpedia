-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_solidCapCone_reflection
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.solidCapCone_reflection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:08:27.987191+00:00
-- url     : https://prove2.me/theorems/33cb43a8-ce46-42f7-af4a-db9598f645ce
-- title:
--   Spherical Cap: solid Cap Cone reflection
-- statement:
--   The Spherical Cap construction uses the solid Cap Cone reflection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L9-L17
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Area.lean#L9-L17

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.solidCapCone_reflection (u v : Sphere) (c : ℝ) :
    solidCapCone u c = axisReflection (u : Space) (v : Space) ⁻¹' solidCapCone v c := by sorry
