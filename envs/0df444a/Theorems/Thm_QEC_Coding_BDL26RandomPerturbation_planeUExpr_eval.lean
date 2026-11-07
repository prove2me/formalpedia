-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_planeUExpr_eval
-- name    : QEC.Coding.BDL26RandomPerturbation.planeUExpr_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:12:00.417308+00:00
-- url     : https://prove2.me/theorems/f281f424-6baa-46a2-a8fd-2edef9205e1c
-- title:
--   BDL26 Random Perturbation: plane UExpr eval
-- statement:
--   The BDL26 Random Perturbation construction uses the plane UExpr eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L163-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L163-L176

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.planeUExpr_eval (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    planeUExpr.eval a z ρ = planeU (a 1-a 0) (a 2-a 0) (z-a 0) := by sorry
