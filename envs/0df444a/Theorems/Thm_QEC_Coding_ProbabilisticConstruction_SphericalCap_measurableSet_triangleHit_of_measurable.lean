-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_triangleHit_of_measurable
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_triangleHit_of_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:45:56.926028+00:00
-- url     : https://prove2.me/theorems/bfd00a48-9def-404f-9a77-4c852ecd9864
-- title:
--   Spherical Cap: measurable Set triangle Hit of measurable
-- statement:
--   Joint Borel input data pull back the actual convex-hull hit relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/JointTriangleHit.lean#L55-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/JointTriangleHit.lean#L55-L69

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_triangleHit_of_measurable {Y : Type*} [MeasurableSpace Y]
    (r p : Y → Fin 3 → Space) (z : Y → Space) (ρ : Y → ℝ)
    (hr : Measurable r) (hp : Measurable p) (hz : Measurable z) (hρ : Measurable ρ) :
    MeasurableSet {y | p y ∈ triangleHit (r y) (z y) (ρ y)} := by sorry
