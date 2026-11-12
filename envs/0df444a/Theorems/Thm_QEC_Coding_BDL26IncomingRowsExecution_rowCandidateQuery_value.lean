-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowCandidateQuery_value
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowCandidateQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:56:07.65192+00:00
-- url     : https://prove2.me/theorems/ffdaa6b2-13ff-4874-96fd-2a9ba91e7c00
-- title:
--   BDL26 Incoming Rows Execution: row Candidate Query value
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Candidate Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L307-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L307-L310

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowCandidateQuery_value (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) :
    (rowCandidateQuery P I hr L).1=(candidateEventQuery P (statePoints I) hr L).1 := by sorry
