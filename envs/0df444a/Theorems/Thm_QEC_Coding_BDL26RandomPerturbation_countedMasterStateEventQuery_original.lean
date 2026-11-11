-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_countedMasterStateEventQuery_original
-- name    : QEC.Coding.BDL26RandomPerturbation.countedMasterStateEventQuery_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:10:42.479595+00:00
-- url     : https://prove2.me/theorems/e351eb70-262b-45b5-8e8f-c2a61dc5cb42
-- title:
--   BDL26 Random Perturbation: counted Master State Event Query original
-- statement:
--   The BDL26 Random Perturbation construction uses the counted Master State Event Query original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L462-L465
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L462-L465

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

theorem QEC.Coding.BDL26RandomPerturbation.countedMasterStateEventQuery_original (P : TannerSquarePresentation)
    (J : Vertex P → Space) (r lambda : ℝ) (K : ℕ) (e : Event P J r) (R : StateRows P) :
    countedMasterStateEventQuery P J lambda K (eventToMaster P J r e) R =
      stateEventQuery P J r lambda K e R := by sorry
