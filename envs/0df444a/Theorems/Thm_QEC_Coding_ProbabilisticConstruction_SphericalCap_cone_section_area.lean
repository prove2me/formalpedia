-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_cone_section_area
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.cone_section_area
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:53:45.699285+00:00
-- url     : https://prove2.me/theorems/aac48651-e331-4793-a69a-a99517a2f539
-- title:
--   Spherical Cap: cone section area
-- statement:
--   The Spherical Cap construction uses the cone section area property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeVolume.lean#L8-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeVolume.lean#L8-L30

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.cone_section_area {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (z : ℝ) :
    volume {y : Transverse | axialEquiv.symm (z,y) ∈ axialCone c} =
      (Icc 0 c).indicator (fun z => ENNReal.ofReal (Real.pi * (coneSlopeSq c * z^2))) z +
      (Ioc c 1).indicator (fun z => ENNReal.ofReal (Real.pi * (1-z^2))) z := by sorry
