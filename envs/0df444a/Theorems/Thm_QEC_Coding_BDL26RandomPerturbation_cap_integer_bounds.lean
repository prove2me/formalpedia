-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_cap_integer_bounds
-- name    : QEC.Coding.BDL26RandomPerturbation.cap_integer_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:39:43.953202+00:00
-- url     : https://prove2.me/theorems/dcd9c834-50ac-4626-a04d-9333d79e7caa
-- title:
--   BDL26 Random Perturbation: cap integer bounds
-- statement:
--   Every sufficiently large chosen integer satisfies the cap and width conditions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Parameters.lean#L41-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Parameters.lean#L41-L51

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.cap_integer_bounds {m : ℕ} (hm : 2 ≤ m)
    (hw : 1 < 6 * (m : ℝ) * widthFactor) :
    1 < (m : ℝ) ∧ 1 < 2 * (m : ℝ) ∧ 2 * (m : ℝ) < 6 * m ∧
      0 < 6 * (m : ℝ) * widthFactor - 1 ∧
      0 < 1 / (12 * (m : ℝ)) ∧ 1 / (12 * (m : ℝ)) < Real.pi := by sorry
