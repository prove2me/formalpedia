-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_zone_ae_cap_difference
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.zone_ae_cap_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:22.028119+00:00
-- url     : https://prove2.me/theorems/e9349627-6262-4e56-b73a-6f930046ed09
-- title:
--   Spherical Cap: zone ae cap difference
-- statement:
--   The Spherical Cap construction uses the zone ae cap difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Zones.lean#L46-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Zones.lean#L46-L56

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.zone_ae_cap_difference (u : Sphere) (a b : ℝ) :
    zone u a b =ᵐ[area] (cap u a \ cap u b : Set Sphere) := by sorry
