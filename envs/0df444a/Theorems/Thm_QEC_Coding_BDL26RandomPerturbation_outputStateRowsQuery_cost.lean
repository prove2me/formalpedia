-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_outputStateRowsQuery_cost
-- name    : QEC.Coding.BDL26RandomPerturbation.outputStateRowsQuery_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:26:23.221135+00:00
-- url     : https://prove2.me/theorems/1755d439-8e23-445f-ae8b-ebc35223c081
-- title:
--   BDL26 Random Perturbation: output State Rows Query cost
-- statement:
--   The BDL26 Random Perturbation construction uses the output State Rows Query cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L618-L621
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L618-L621

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

theorem QEC.Coding.BDL26RandomPerturbation.outputStateRowsQuery_cost (P : TannerSquarePresentation)
    (J : Vertex P → Space) (lambda : ℝ) (R : StateRows P) :
    (outputStateRowsQuery P J lambda R).2 = R.length * 28 := by sorry
