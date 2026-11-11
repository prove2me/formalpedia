-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowExecutionQuery_embedding_rows
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowExecutionQuery_embedding_rows
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T03:28:52.84632+00:00
-- url     : https://prove2.me/theorems/355b07c0-b399-4a0d-9926-5e1e83fa171c
-- title:
--   BDL26 Incoming Rows Execution: row Execution Query embedding rows
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Execution Query embedding rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L686-L692
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L686-L692

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowExecutionQuery_embedding_rows (P : TannerSquarePresentation) (I : StateRows P)
    {L : ℝ} (p : GeometricParameters L) (T : Table (X := fun _ : Vertex P => Space)) :
    (rowExecutionQuery P I (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) T).1 =
      (vertexInputList P).map (fun v => (v,perturbationEmbeddingOutput P (statePoints I) p T v)) := by sorry
