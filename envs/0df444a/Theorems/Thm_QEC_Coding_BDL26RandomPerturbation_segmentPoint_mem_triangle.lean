-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_segmentPoint_mem_triangle
-- name    : QEC.Coding.BDL26RandomPerturbation.segmentPoint_mem_triangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:55.330357+00:00
-- url     : https://prove2.me/theorems/f26272b7-3f6a-4e8f-a882-be312637b9d0
-- title:
--   BDL26 Random Perturbation: segment Point mem triangle
-- statement:
--   The BDL26 Random Perturbation construction uses the segment Point mem triangle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleDecision.lean#L21-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleDecision.lean#L21-L26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SingularTriangle
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.segmentPoint_mem_triangle (a : Fin 3 → Space) (z : Space) (i j : Fin 3) :
    segmentPoint (a i) (a j) z ∈ convexHull ℝ (range a) := by sorry
