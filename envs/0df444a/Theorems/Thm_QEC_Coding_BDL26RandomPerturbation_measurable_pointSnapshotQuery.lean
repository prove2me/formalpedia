-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_pointSnapshotQuery
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_pointSnapshotQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:09:57.174194+00:00
-- url     : https://prove2.me/theorems/1c28a730-3485-46a9-9c34-0c87b724f6c6
-- title:
--   BDL26 Random Perturbation: measurable point Snapshot Query
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable point Snapshot Query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L389-L398
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L389-L398

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_pointSnapshotQuery {Ω : Type*} [MeasurableSpace Ω]
    (lambda : ℝ) (a b : Ω → Space) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun w => pointSnapshotQuery lambda (a w) (b w)) := by sorry
