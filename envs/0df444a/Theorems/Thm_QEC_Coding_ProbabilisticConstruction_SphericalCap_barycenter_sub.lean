-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenter_sub
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenter_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:03.189779+00:00
-- url     : https://prove2.me/theorems/6a6f3187-6a99-4e45-b419-2a1c23185b13
-- title:
--   Spherical Cap: barycenter sub
-- statement:
--   The Spherical Cap construction uses the barycenter sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L135-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L135-L142

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenter_sub (a : Fin 3 → Space) (z : Space)
    (w : stdSimplex ℝ (Fin 3)) :
    (∑ j, (w : Fin 3 → ℝ) j • a j)-z =
      ∑ j, (w : Fin 3 → ℝ) j • (a j-z) := by sorry
