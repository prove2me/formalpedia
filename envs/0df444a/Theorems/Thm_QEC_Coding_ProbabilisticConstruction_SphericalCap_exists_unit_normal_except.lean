-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_exists_unit_normal_except
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.exists_unit_normal_except
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:10:41.974348+00:00
-- url     : https://prove2.me/theorems/46b41ffd-55fa-4bf4-9b48-6c9227c05482
-- title:
--   Spherical Cap: exists unit normal except
-- statement:
--   The Spherical Cap construction uses the exists unit normal except property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L53-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L53-L61

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.exists_unit_normal_except (a : Fin 3 → Space) (z : Space) (i : Fin 3) :
    ∃ n : Sphere, ∀ j, j ≠ i → inner ℝ (n : Space) (a j-z) = 0 := by sorry
