-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_filterMapQuery
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_filterMapQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:09:28.617818+00:00
-- url     : https://prove2.me/theorems/42cd7d1f-826e-41e4-a64b-9182b3147477
-- title:
--   BDL26 Random Perturbation: measurable filter Map Query
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable filter Map Query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L251-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L251-L262

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
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListMeasurable
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListSingleton

theorem QEC.Coding.BDL26RandomPerturbation.measurable_filterMapQuery {Ω A B : Type*} [MeasurableSpace Ω]
    [Countable B] [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace (Option B)] [MeasurableSingletonClass (Option B)]
    (q : A → Ω → Option B × ℕ) (hq : ∀ a, Measurable (q a)) (L : List A) :
    Measurable (fun w => filterMapQuery (fun a => q a w) L) := by sorry
