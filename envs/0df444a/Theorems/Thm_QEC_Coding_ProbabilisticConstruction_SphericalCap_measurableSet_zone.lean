-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_zone
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_zone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:23.631409+00:00
-- url     : https://prove2.me/theorems/82c8b738-23fd-4472-9cf0-0736b732e56e
-- title:
--   Spherical Cap: measurable Set zone
-- statement:
--   The Spherical Cap construction uses the measurable Set zone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Zones.lean#L40-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Zones.lean#L40-L44

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_zone (u : Sphere) (a b : ℝ) : MeasurableSet (zone u a b) := by sorry
