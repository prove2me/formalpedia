-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_triangleQuery
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_triangleQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:08:52.793964+00:00
-- url     : https://prove2.me/theorems/3d080b04-416b-4a75-8e14-f390a2413ded
-- title:
--   BDL26 Random Perturbation: measurable triangle Query
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable triangle Query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L88-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L88-L93

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_triangleQuery {Ω : Type*} [MeasurableSpace Ω]
    (a : Ω → Fin 3 → Space) (z : Ω → Space) (ρ : Ω → ℝ)
    (ha : ∀ i j, Measurable (fun w => a w i j))
    (hz : ∀ j, Measurable (fun w => z w j)) (hρ : Measurable ρ) :
    Measurable (fun w => triangleQuery (a w) (z w) (ρ w)) := by sorry
