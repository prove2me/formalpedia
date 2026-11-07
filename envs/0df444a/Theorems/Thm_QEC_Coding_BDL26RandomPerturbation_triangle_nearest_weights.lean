-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangle_nearest_weights
-- name    : QEC.Coding.BDL26RandomPerturbation.triangle_nearest_weights
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:36.394473+00:00
-- url     : https://prove2.me/theorems/32936ca9-aea2-4aa8-bed8-4c8cebcf3143
-- title:
--   BDL26 Random Perturbation: triangle nearest weights
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle nearest weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleMinimum.lean#L24-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleMinimum.lean#L24-L40

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleMinimum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.triangle_nearest_weights (a : Fin 3 → Space) (z : Space) :
    ∃ w : stdSimplex ℝ (Fin 3),
      (∀ x ∈ convexHull ℝ (range a),
        dist z (barycenterMap a w) ≤ dist z x) ∧
      ∀ i, inner ℝ (z-barycenterMap a w) (a i-barycenterMap a w) ≤ 0 := by sorry
