-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_all
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:15.158021+00:00
-- url     : https://prove2.me/theorems/839e4fbd-def8-4720-81f3-12521154a91e
-- title:
--   Spherical Cap: area cap all
-- statement:
--   The Spherical Cap construction uses the area cap all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Zones.lean#L13-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Zones.lean#L13-L35

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_all (u : Sphere) (c : ℝ) :
    area (cap u c) = ENNReal.ofReal (2 * Real.pi * capHeight c) := by sorry
