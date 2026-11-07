-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_zone
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.area_zone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:33.430549+00:00
-- url     : https://prove2.me/theorems/d45cbfa7-8662-4836-aee2-db44e100a97e
-- title:
--   Spherical Cap: area zone
-- statement:
--   The Spherical Cap construction uses the area zone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Zones.lean#L63-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Zones.lean#L63-L73

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.area_zone (u : Sphere) {a b : ℝ} (hab : a ≤ b) :
    area (zone u a b) = ENNReal.ofReal (2 * Real.pi * max 0 (min 1 b - max (-1) a)) := by sorry
