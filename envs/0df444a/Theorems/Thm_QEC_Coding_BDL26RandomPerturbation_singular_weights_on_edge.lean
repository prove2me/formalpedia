-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_singular_weights_on_edge
-- name    : QEC.Coding.BDL26RandomPerturbation.singular_weights_on_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:54.420254+00:00
-- url     : https://prove2.me/theorems/6a52d066-7dc9-4815-808a-1cd38c1073b3
-- title:
--   BDL26 Random Perturbation: singular weights on edge
-- statement:
--   The singular Gram case includes repeated vertices and collinear triples.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SingularTriangle.lean#L70-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SingularTriangle.lean#L70-L82

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleMinimum
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SingularTriangle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.singular_weights_on_edge (a : Fin 3 → Space)
    (w : stdSimplex ℝ (Fin 3)) (hdet : gramDet (a 1-a 0) (a 2-a 0) = 0) :
    ∃ i j : Fin 3, i < j ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      barycenterMap a w = a i+t • (a j-a i) := by sorry
