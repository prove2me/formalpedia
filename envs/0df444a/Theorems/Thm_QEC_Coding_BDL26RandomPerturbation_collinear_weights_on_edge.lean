-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_collinear_weights_on_edge
-- name    : QEC.Coding.BDL26RandomPerturbation.collinear_weights_on_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:45.83373+00:00
-- url     : https://prove2.me/theorems/b30daa39-3c34-4177-9c2d-ea22c50513ad
-- title:
--   BDL26 Random Perturbation: collinear weights on edge
-- statement:
--   The BDL26 Random Perturbation construction uses the collinear weights on edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SingularTriangle.lean#L10-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SingularTriangle.lean#L10-L67

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleMinimum
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SingularTriangle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.collinear_weights_on_edge (a : Fin 3 → Space)
    (w : stdSimplex ℝ (Fin 3)) (k : ℝ)
    (hk : a 2-a 0 = k • (a 1-a 0)) :
    ∃ i j : Fin 3, i < j ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      barycenterMap a w = a i+t • (a j-a i) := by sorry
