-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_triangleHit_eq_union
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.triangleHit_eq_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:09:17.899786+00:00
-- url     : https://prove2.me/theorems/b6f8ba33-46bb-489c-b88b-1cf976bbc691
-- title:
--   Spherical Cap: triangle Hit eq union
-- statement:
--   The Spherical Cap construction uses the triangle Hit eq union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L118-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L118-L128

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.triangleHit_eq_union (r : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    triangleHit r z ρ = ⋃ i, largeWeightHit r z ρ i := by sorry
