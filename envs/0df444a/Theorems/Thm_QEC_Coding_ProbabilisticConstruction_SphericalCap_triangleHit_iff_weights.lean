-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_triangleHit_iff_weights
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.triangleHit_iff_weights
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:09:13.767791+00:00
-- url     : https://prove2.me/theorems/2c07181d-71c2-44bb-99f9-ba02af0a1960
-- title:
--   Spherical Cap: triangle Hit iff weights
-- statement:
--   The Spherical Cap construction uses the triangle Hit iff weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L66-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L66-L74

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.triangleHit_iff_weights (r : Fin 3 → Space) (z : Space) (ρ : ℝ)
    (p : Fin 3 → Space) : p ∈ triangleHit r z ρ ↔
    ∃ w : stdSimplex ℝ (Fin 3), dist (∑ j, (w : Fin 3 → ℝ) j • (r j+p j)) z ≤ ρ := by sorry
