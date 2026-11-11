-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_realTest_run
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_realTest_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:07:55.918541+00:00
-- url     : https://prove2.me/theorems/a2f3668c-26cb-4f01-825c-2097487a1333
-- title:
--   BDL26 Random Perturbation: measurable real Test run
-- statement:
--   The comparison result and its actual cost are proved together.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L65-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L65-L86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal

theorem QEC.Coding.BDL26RandomPerturbation.measurable_realTest_run {Ω : Type*} [MeasurableSpace Ω]
    (a : Ω → Fin 3 → Space) (z : Ω → Space) (ρ : Ω → ℝ)
    (ha : ∀ i j, Measurable (fun w => a w i j))
    (hz : ∀ j, Measurable (fun w => z w j)) (hρ : Measurable ρ) (e : RealTest) :
    Measurable (fun w => e.run (a w) (z w) (ρ w)) := by sorry
