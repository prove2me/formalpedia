-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowOutputQuery_cost
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowOutputQuery_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:21:08.713649+00:00
-- url     : https://prove2.me/theorems/8e534dfb-1ea2-466c-9458-a7a1045f00b4
-- title:
--   BDL26 Incoming Rows Execution: row Output Query cost
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Output Query cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L645-L649
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L645-L649

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Semantics_CompletelyPositive_sum
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowOutputQuery_cost (P : TannerSquarePresentation) (I : StateRows P)
    (lambda : ℝ) (R : StateRows P) :
    (rowOutputQuery P I lambda R).2=(outputStateRowsQuery P (statePoints I) lambda R).2+
      (R.map (fun row => (incomingRead P I row.1).2)).sum := by sorry
