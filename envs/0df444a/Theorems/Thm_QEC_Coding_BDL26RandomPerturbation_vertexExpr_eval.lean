-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexExpr_eval
-- name    : QEC.Coding.BDL26RandomPerturbation.vertexExpr_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:49.824751+00:00
-- url     : https://prove2.me/theorems/b3d12f20-82e0-4a87-929d-48f86b94f744
-- title:
--   BDL26 Random Perturbation: vertex Expr eval
-- statement:
--   The BDL26 Random Perturbation construction uses the vertex Expr eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L124-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L124-L125

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.vertexExpr_eval (i j : Fin 3) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (vertexExpr i j).eval a z ρ = a i j := by sorry

attribute [defeq] QEC.Coding.BDL26RandomPerturbation.vertexExpr_eval
