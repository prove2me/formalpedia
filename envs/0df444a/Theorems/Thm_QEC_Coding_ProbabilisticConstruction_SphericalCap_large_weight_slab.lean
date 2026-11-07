-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_large_weight_slab
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.large_weight_slab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:08.013231+00:00
-- url     : https://prove2.me/theorems/028fe763-8b8e-4710-895f-a968d68c5a9b
-- title:
--   Spherical Cap: large weight slab
-- statement:
--   The Spherical Cap construction uses the large weight slab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L144-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L144-L162

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.large_weight_slab {a : Fin 3 → Space} {z : Space} {ρ : ℝ} {i : Fin 3}
    (w : stdSimplex ℝ (Fin 3)) (hw : (1:ℝ)/3 ≤ (w : Fin 3 → ℝ) i)
    (hball : dist (∑ j, (w : Fin 3 → ℝ) j • a j) z ≤ ρ)
    (n : Sphere) (hn : ∀ j, j ≠ i → inner ℝ (n : Space) (a j-z) = 0) :
    |inner ℝ (n : Space) (a i-z)| ≤ 3*ρ := by sorry
