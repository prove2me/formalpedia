-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_positive_weights_stationary
-- name    : QEC.Coding.BDL26RandomPerturbation.positive_weights_stationary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:40.412664+00:00
-- url     : https://prove2.me/theorems/4fcdd96a-0d55-42dd-b741-409cfef9dff1
-- title:
--   BDL26 Random Perturbation: positive weights stationary
-- statement:
--   The BDL26 Random Perturbation construction uses the positive weights stationary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleMinimum.lean#L55-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleMinimum.lean#L55-L73

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleMinimum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.positive_weights_stationary (a : Fin 3 → Space) (z : Space)
    (w : stdSimplex ℝ (Fin 3)) (hw : ∀ i, 0 < w.val i)
    (hi : ∀ i, inner ℝ (z-barycenterMap a w) (a i-barycenterMap a w) ≤ 0) :
    ∀ i, inner ℝ (z-barycenterMap a w) (a i-barycenterMap a w) = 0 := by sorry
