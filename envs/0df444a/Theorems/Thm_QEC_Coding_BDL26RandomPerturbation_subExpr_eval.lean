-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_subExpr_eval
-- name    : QEC.Coding.BDL26RandomPerturbation.subExpr_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:53.942702+00:00
-- url     : https://prove2.me/theorems/feb9640c-34a5-4673-aa62-830cdadc1510
-- title:
--   BDL26 Random Perturbation: sub Expr eval
-- statement:
--   The BDL26 Random Perturbation construction uses the sub Expr eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L129-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L129-L134

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.subExpr_eval (b c : VecExpr) (a : Fin 3 → Space) (z : Space) (ρ : ℝ)
    (x y : Space) (hx : ∀ j, (b j).eval a z ρ = x j)
    (hy : ∀ j, (c j).eval a z ρ = y j) (j : Fin 3) :
    (subExpr b c j).eval a z ρ = (x-y) j := by sorry
