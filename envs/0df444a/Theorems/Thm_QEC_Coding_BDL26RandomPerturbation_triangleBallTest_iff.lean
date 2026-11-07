-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleBallTest_iff
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleBallTest_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:57.422974+00:00
-- url     : https://prove2.me/theorems/5a484478-c8a5-44b2-8f8d-8bb890a1ab4a
-- title:
--   BDL26 Random Perturbation: triangle Ball Test iff
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle Ball Test iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleDecision.lean#L58-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleDecision.lean#L58-L96

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SingularTriangle
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.triangleBallTest_iff (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    triangleBallTest a z ρ ↔ ∃ y ∈ convexHull ℝ (range a), dist y z ≤ ρ := by sorry
