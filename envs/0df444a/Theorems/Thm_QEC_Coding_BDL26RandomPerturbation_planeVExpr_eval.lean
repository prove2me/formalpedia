-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_planeVExpr_eval
-- name    : QEC.Coding.BDL26RandomPerturbation.planeVExpr_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:12:01.768702+00:00
-- url     : https://prove2.me/theorems/fe626142-8805-471d-96f8-7bccf86ba642
-- title:
--   BDL26 Random Perturbation: plane VExpr eval
-- statement:
--   The BDL26 Random Perturbation construction uses the plane VExpr eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L178-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L178-L191

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.planeVExpr_eval (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    planeVExpr.eval a z ρ = planeV (a 1-a 0) (a 2-a 0) (z-a 0) := by sorry
