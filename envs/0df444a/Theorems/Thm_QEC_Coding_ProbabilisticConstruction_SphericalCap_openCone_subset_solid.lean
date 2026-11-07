-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_openCone_subset_solid
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.openCone_subset_solid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:53:01.267678+00:00
-- url     : https://prove2.me/theorems/bc39cdba-6cfa-4274-b8c8-8d4b891b72fb
-- title:
--   Spherical Cap: open Cone subset solid
-- statement:
--   The Spherical Cap construction uses the open Cone subset solid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeBridge.lean#L17-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeBridge.lean#L17-L24

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.openCone_subset_solid (u : Sphere) (c : ℝ) :
    Ioo (0 : ℝ) 1 • ((↑) '' cap u c) ⊆ solidCapCone u c := by sorry
