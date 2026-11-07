-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_volume_axialCone
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.volume_axialCone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:55:41.997029+00:00
-- url     : https://prove2.me/theorems/48be7b92-c5b8-499a-acfb-821fcdf4d1eb
-- title:
--   Spherical Cap: volume axial Cone
-- statement:
--   The Spherical Cap construction uses the volume axial Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeVolume.lean#L32-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeVolume.lean#L32-L78

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.volume_axialCone {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    (volume : Measure Ambient) (axialCone c) =
      ENNReal.ofReal ((2 * Real.pi / 3) * (1-c)) := by sorry
