-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealTest_run_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.RealTest.run_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:21:34.92242+00:00
-- url     : https://prove2.me/theorems/e3fe83b9-74cb-4c77-8862-113bf29143ea
-- title:
--   Real Test: run cost le
-- statement:
--   The Real Test construction uses the run cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L296-L308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L296-L308

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.RealTest.run_cost_le (e : RealTest) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (e.run a z ρ).2 ≤ 2*e.cost := by sorry
