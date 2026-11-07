-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleQueryProgram_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.triangleQueryProgram_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:21:16.754967+00:00
-- url     : https://prove2.me/theorems/d41d14d6-e1fe-4440-9da8-afcfd14610f3
-- title:
--   BDL26 Random Perturbation: triangle Query Program correct
-- statement:
--   The BDL26 Random Perturbation construction uses the triangle Query Program correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L211-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean#L211-L237

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.triangleQueryProgram_correct (a : Fin 3 → Space) (z : Space) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : triangleQueryProgram.eval a z ρ = true ↔
      ∃ y ∈ convexHull ℝ (Set.range a), dist y z ≤ ρ := by sorry
