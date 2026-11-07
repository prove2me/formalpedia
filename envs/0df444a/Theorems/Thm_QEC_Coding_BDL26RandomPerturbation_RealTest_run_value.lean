-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealTest_run_value
-- name    : QEC.Coding.BDL26RandomPerturbation.RealTest.run_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:21:26.083206+00:00
-- url     : https://prove2.me/theorems/7bb6c004-5ab1-4643-b4db-215a896f3ab4
-- title:
--   Real Test: run value
-- statement:
--   The Real Test construction uses the run value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L292-L294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L292-L294

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.RealTest.run_value (e : RealTest) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (e.run a z ρ).1 = e.eval a z ρ := by sorry
