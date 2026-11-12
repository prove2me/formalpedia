-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowOutputQuery_value
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowOutputQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:18:44.93008+00:00
-- url     : https://prove2.me/theorems/16fe9a63-ee5c-472c-97b0-4ee5a336931f
-- title:
--   BDL26 Incoming Rows Execution: row Output Query value
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Output Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L640-L643
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L640-L643

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26IncomingRowsExecution
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] BDL26RandomPerturbation.countedLabelListMeasurable
  BDL26RandomPerturbation.countedLabelListSingleton

theorem QEC.Coding.BDL26IncomingRowsExecution.rowOutputQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (R : StateRows P) :
    (rowOutputQuery P I lambda R).1=(outputStateRowsQuery P (statePoints I) lambda R).1 := by sorry
