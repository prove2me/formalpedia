-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_distanceTest_eval
-- name    : QEC.Coding.BDL26RandomPerturbation.distanceTest_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:21:14.07864+00:00
-- url     : https://prove2.me/theorems/0fafec15-1143-4735-bf7b-84af6d4031a4
-- title:
--   BDL26 Random Perturbation: distance Test eval
-- statement:
--   The BDL26 Random Perturbation construction uses the distance Test eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L199-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L199-L209

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.distanceTest_eval (b : VecExpr) (a : Fin 3 → Space) (z : Space) (ρ : ℝ)
    (x : Space) (hx : ∀ j, (b j).eval a z ρ = x j) (hρ : 0 ≤ ρ) :
    (distanceTest b).eval a z ρ = true ↔ dist z x ≤ ρ := by sorry
