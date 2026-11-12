-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowCandidateQuery_cost_le
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowCandidateQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:56:26.354554+00:00
-- url     : https://prove2.me/theorems/f6d2adc0-1651-40bc-9fa2-cfbad07283f1
-- title:
--   BDL26 Incoming Rows Execution: row Candidate Query cost le
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Candidate Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L312-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L312-L314

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowCandidateQuery_cost_le (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) : (rowCandidateQuery P I hr L).2 ≤
      accessMultiplier I*(candidateEventQuery P (statePoints I) hr L).2 := by sorry
