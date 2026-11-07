-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_planeExpr_eval
-- name    : QEC.Coding.BDL26RandomPerturbation.planeExpr_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:21:13.647559+00:00
-- url     : https://prove2.me/theorems/209b7efd-7268-45b8-9bcb-a87464d435d3
-- title:
--   BDL26 Random Perturbation: plane Expr eval
-- statement:
--   The BDL26 Random Perturbation construction uses the plane Expr eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L193-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L193-L197

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.planeExpr_eval (j : Fin 3) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (planeExpr j).eval a z ρ = planePoint a z j := by sorry
