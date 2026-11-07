-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_exists_unit_normal_pair
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.exists_unit_normal_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:10:58.690605+00:00
-- url     : https://prove2.me/theorems/ef032b63-81b9-41d7-8293-a90b1e6fda89
-- title:
--   Spherical Cap: exists unit normal pair
-- statement:
--   The Spherical Cap construction uses the exists unit normal pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L11-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean#L11-L37

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.exists_unit_normal_pair (b c : Space) :
    ∃ n : Space, ‖n‖ = 1 ∧ inner ℝ n b = 0 ∧ inner ℝ n c = 0 := by sorry
