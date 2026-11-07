-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_isClosed_largeWeightHit
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.isClosed_largeWeightHit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:09:13.686195+00:00
-- url     : https://prove2.me/theorems/3a43ab94-c258-43db-b533-e6bf94e7b3be
-- title:
--   Spherical Cap: is Closed large Weight Hit
-- statement:
--   The Spherical Cap construction uses the is Closed large Weight Hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L90-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L90-L116

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.isClosed_largeWeightHit (r : Fin 3 → Space) (z : Space) (ρ : ℝ) (i : Fin 3) :
    IsClosed (largeWeightHit r z ρ i) := by sorry
