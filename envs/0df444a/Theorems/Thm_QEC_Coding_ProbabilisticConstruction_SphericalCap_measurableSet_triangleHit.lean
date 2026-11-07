-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_triangleHit
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_triangleHit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:00.658101+00:00
-- url     : https://prove2.me/theorems/db6df5cb-e23d-4e7f-8d18-a6ca97278c6c
-- title:
--   Spherical Cap: measurable Set triangle Hit
-- statement:
--   The Spherical Cap construction uses the measurable Set triangle Hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L130-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L130-L133

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_triangleHit (r : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    MeasurableSet (triangleHit r z ρ) := by sorry
