-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_mem_openCone_of_mem_solid
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.mem_openCone_of_mem_solid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:53:05.196669+00:00
-- url     : https://prove2.me/theorems/52f9294b-d478-49a8-82a5-95b64228e718
-- title:
--   Spherical Cap: mem open Cone of mem solid
-- statement:
--   The Spherical Cap construction uses the mem open Cone of mem solid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeBridge.lean#L26-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/ConeBridge.lean#L26-L40

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.mem_openCone_of_mem_solid (u : Sphere) (c : ℝ) {x : Space}
    (hx : x ∈ solidCapCone u c) (h0 : x ≠ 0) (h1 : ‖x‖ ≠ 1) :
    x ∈ Ioo (0 : ℝ) 1 • ((↑) '' cap u c) := by sorry
