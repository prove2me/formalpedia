-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_dotExpr_eval
-- name    : QEC.Coding.BDL26RandomPerturbation.dotExpr_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:40.591149+00:00
-- url     : https://prove2.me/theorems/8c9e8c9e-de9f-42e9-8f38-6754e197e28a
-- title:
--   BDL26 Random Perturbation: dot Expr eval
-- statement:
--   The BDL26 Random Perturbation construction uses the dot Expr eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L116-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L116-L122

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.dotExpr_eval (b c : VecExpr) (a : Fin 3 → Space) (z : Space) (ρ : ℝ)
    (x y : Space) (hx : ∀ j, (b j).eval a z ρ = x j)
    (hy : ∀ j, (c j).eval a z ρ = y j) :
    (dotExpr b c).eval a z ρ = inner ℝ x y := by sorry
