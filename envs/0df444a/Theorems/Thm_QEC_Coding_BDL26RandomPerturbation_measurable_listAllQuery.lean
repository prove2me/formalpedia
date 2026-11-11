-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_listAllQuery
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_listAllQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:09:27.482839+00:00
-- url     : https://prove2.me/theorems/2f360313-77dd-438d-883f-45632c278de0
-- title:
--   BDL26 Random Perturbation: measurable list All Query
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable list All Query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L95-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L95-L102

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_listAllQuery {Ω A : Type*} [MeasurableSpace Ω]
    (q : A → Ω → Bool × ℕ) (hq : ∀ a, Measurable (q a)) (L : List A) :
    Measurable (fun w => listAllQuery (fun a => q a w) L) := by sorry
