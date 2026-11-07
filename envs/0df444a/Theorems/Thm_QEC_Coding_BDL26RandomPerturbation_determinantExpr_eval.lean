-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_determinantExpr_eval
-- name    : QEC.Coding.BDL26RandomPerturbation.determinantExpr_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:58.83295+00:00
-- url     : https://prove2.me/theorems/b0e48c31-ac31-4126-adf3-7af2114bc44e
-- title:
--   BDL26 Random Perturbation: determinant Expr eval
-- statement:
--   The BDL26 Random Perturbation construction uses the determinant Expr eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L149-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L149-L158

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.determinantExpr_eval (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    determinantExpr.eval a z ρ = gramDet (a 1-a 0) (a 2-a 0) := by sorry
