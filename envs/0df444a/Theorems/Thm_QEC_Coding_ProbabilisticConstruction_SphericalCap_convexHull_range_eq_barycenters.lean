-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_convexHull_range_eq_barycenters
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.convexHull_range_eq_barycenters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:08:43.198783+00:00
-- url     : https://prove2.me/theorems/b3f5b763-9a1d-480f-ab7e-008f24cb5229
-- title:
--   Spherical Cap: convex Hull range eq barycenters
-- statement:
--   The Spherical Cap construction uses the convex Hull range eq barycenters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L45-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L45-L51

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.convexHull_range_eq_barycenters (a : Fin 3 → Space) :
    convexHull ℝ (range a) = barycenterMap a '' stdSimplex ℝ (Fin 3) := by sorry
