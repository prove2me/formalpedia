-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_boundary_weights_on_edge
-- name    : QEC.Coding.BDL26RandomPerturbation.boundary_weights_on_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:40.755215+00:00
-- url     : https://prove2.me/theorems/6c05c437-a681-404b-bab1-1cf9e4591279
-- title:
--   BDL26 Random Perturbation: boundary weights on edge
-- statement:
--   The BDL26 Random Perturbation construction uses the boundary weights on edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleMinimum.lean#L75-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleMinimum.lean#L75-L102

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleMinimum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.boundary_weights_on_edge (a : Fin 3 → Space) (w : stdSimplex ℝ (Fin 3))
    (hw : ∃ i, w.val i = 0) :
    ∃ i j : Fin 3, i < j ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      barycenterMap a w = a i+t • (a j-a i) := by sorry
