-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_incomingRows_read_cost
-- name    : QEC.Coding.BDL26IncomingRowsExecution.incomingRows_read_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:30:46.380363+00:00
-- url     : https://prove2.me/theorems/a5f76f79-b4d1-4b76-bd6c-a97e4aa92150
-- title:
--   BDL26 Incoming Rows Execution: incoming Rows read cost
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the incoming Rows read cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L917-L920
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L917-L920

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

theorem QEC.Coding.BDL26IncomingRowsExecution.incomingRows_read_cost (P : TannerSquarePresentation) (J : Vertex P → Space)
    (v : Vertex P) : (incomingRead P (incomingRows P J) v).2=
      (incomingRead P (incomingRows P (fun _ => 0)) v).2 := by sorry
