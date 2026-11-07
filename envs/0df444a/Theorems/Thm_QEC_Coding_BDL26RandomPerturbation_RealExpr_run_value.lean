-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealExpr_run_value
-- name    : QEC.Coding.BDL26RandomPerturbation.RealExpr.run_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:47.294948+00:00
-- url     : https://prove2.me/theorems/0453c8a3-cf30-4864-a145-2da1fb4087ea
-- title:
--   Real Expr: run value
-- statement:
--   The Real Expr construction uses the run value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L265-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L265-L270

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.RealExpr.run_value (e : RealExpr) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (e.run a z ρ).1 = e.eval a z ρ := by sorry
