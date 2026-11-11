-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_fullCenterQuery
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_fullCenterQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:11:31.218203+00:00
-- url     : https://prove2.me/theorems/89f7e65d-dd8d-41d8-a939-ffa86882e957
-- title:
--   BDL26 Random Perturbation: measurable full Center Query
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable full Center Query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L467-L480
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L467-L480

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_fullCenterQuery {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) (lambda : ℝ) (K : ℕ)
    (a : Option (Triangle P)) (g : Grid K) (J : Ω → Vertex P → Space)
    (hJ : Measurable J) :
    Measurable (fun w => fullCenterQuery P (J w) lambda K a g) := by sorry
