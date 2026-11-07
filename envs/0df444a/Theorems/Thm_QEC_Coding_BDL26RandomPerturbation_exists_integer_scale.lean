-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_exists_integer_scale
-- name    : QEC.Coding.BDL26RandomPerturbation.exists_integer_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:39:49.70971+00:00
-- url     : https://prove2.me/theorems/8cc329a2-5ae2-4ac3-a673-06a670d80572
-- title:
--   BDL26 Random Perturbation: exists integer scale
-- statement:
--   Integral scale choice makes the later finite lattice cubes explicit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Parameters.lean#L83-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Parameters.lean#L83-L90

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.exists_integer_scale {alpha probabilityConstant : ℝ} (ha : 0 ≤ alpha) (D : ℕ) :
    ∃ lambda : ℕ, 1 ≤ lambda ∧ 13 ≤ (2*alpha+1)*(lambda : ℝ) ∧
      4*probabilityConstant*(D+1) ≤ (lambda : ℝ) := by sorry
