-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_isClosed_triangleHit_of_continuous
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.isClosed_triangleHit_of_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:22:04.923741+00:00
-- url     : https://prove2.me/theorems/8561b8f1-87a8-47a2-a777-6d7c83b3b32c
-- title:
--   Spherical Cap: is Closed triangle Hit of continuous
-- statement:
--   Compact barycentric witnesses give a closed relation for all varying data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/JointTriangleHit.lean#L14-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/JointTriangleHit.lean#L14-L43

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.isClosed_triangleHit_of_continuous {Y : Type*} [TopologicalSpace Y]
    (r p : Y → Fin 3 → Space) (z : Y → Space) (ρ : Y → ℝ)
    (hr : Continuous r) (hp : Continuous p) (hz : Continuous z) (hρ : Continuous ρ) :
    IsClosed {y | p y ∈ triangleHit (r y) (z y) (ρ y)} := by sorry
