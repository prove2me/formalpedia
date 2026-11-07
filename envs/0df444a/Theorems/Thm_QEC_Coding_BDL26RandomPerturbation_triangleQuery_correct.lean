-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleQuery_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleQuery_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:45:17.555513+00:00
-- url     : https://prove2.me/theorems/cb4809c4-f7bf-4bba-9971-b57f45584419
-- title:
--   BDL26 Random Perturbation: triangle Query correct
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle Query correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L313-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L313-L316

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.triangleQuery_correct (a : Fin 3 → Space) (z : Space) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (triangleQuery a z ρ).1 = true ↔
      ∃ y ∈ convexHull ℝ (Set.range a), dist y z ≤ ρ := by sorry
