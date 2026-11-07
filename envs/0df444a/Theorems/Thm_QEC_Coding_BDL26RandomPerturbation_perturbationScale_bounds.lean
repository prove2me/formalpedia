-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_perturbationScale_bounds
-- name    : QEC.Coding.BDL26RandomPerturbation.perturbationScale_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:10:28.475199+00:00
-- url     : https://prove2.me/theorems/4a0966fc-bb9d-4930-ae06-651ff82621e0
-- title:
--   BDL26 Random Perturbation: perturbation Scale bounds
-- statement:
--   The BDL26 Random Perturbation construction uses the perturbation Scale bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Parameters.lean#L67-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Parameters.lean#L67-L80

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.perturbationScale_bounds {alpha probabilityConstant : ℝ} (ha : 0 ≤ alpha) (D : ℕ) :
    1 ≤ perturbationScale alpha probabilityConstant D ∧
      13 ≤ (2 * alpha + 1) * perturbationScale alpha probabilityConstant D ∧
      4 * probabilityConstant * (D + 1) ≤ perturbationScale alpha probabilityConstant D := by sorry
