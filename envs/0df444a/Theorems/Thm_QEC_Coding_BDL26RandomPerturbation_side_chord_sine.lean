-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_side_chord_sine
-- name    : QEC.Coding.BDL26RandomPerturbation.side_chord_sine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:38:58.98222+00:00
-- url     : https://prove2.me/theorems/6b878870-5c37-4aea-b3b7-abe4248721c1
-- title:
--   BDL26 Random Perturbation: side chord sine
-- statement:
--   The side estimate uses angle one third, not the weaker width angle one sixth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Parameters.lean#L17-L19
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Parameters.lean#L17-L19

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.side_chord_sine : (1 : ℝ) / 6 ≤ 2 * Real.sin (1 / 6) := by sorry
