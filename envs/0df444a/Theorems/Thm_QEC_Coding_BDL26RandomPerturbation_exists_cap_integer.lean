-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_exists_cap_integer
-- name    : QEC.Coding.BDL26RandomPerturbation.exists_cap_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:39:30.671196+00:00
-- url     : https://prove2.me/theorems/4f706340-30cb-49c1-bafd-da14294f9390
-- title:
--   BDL26 Random Perturbation: exists cap integer
-- statement:
--   Choose an integer cap scale with positive source width; no numeric witness is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Parameters.lean#L29-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Parameters.lean#L29-L38

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.exists_cap_integer : ∃ m : ℕ, 2 ≤ m ∧ 1 < 6 * (m : ℝ) * widthFactor := by sorry
