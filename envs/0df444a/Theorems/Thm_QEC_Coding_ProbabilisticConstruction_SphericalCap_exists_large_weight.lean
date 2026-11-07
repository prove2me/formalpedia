-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_exists_large_weight
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.exists_large_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:10:42.672976+00:00
-- url     : https://prove2.me/theorems/23df359c-e2f4-40c8-8b4e-63c9fe4dffb4
-- title:
--   Spherical Cap: exists large weight
-- statement:
--   The Spherical Cap construction uses the exists large weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L77-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L77-L83

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.exists_large_weight {w : Fin 3 → ℝ} (hw : w ∈ stdSimplex ℝ (Fin 3)) :
    ∃ i, (1:ℝ)/3 ≤ w i := by sorry
