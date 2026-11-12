-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowUniverseQuery_order
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowUniverseQuery_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:18:27.74745+00:00
-- url     : https://prove2.me/theorems/bc20b24a-8fc1-4625-a305-23c8675a6ee2
-- title:
--   BDL26 Incoming Rows Execution: row Universe Query order
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Universe Query order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1409-L1413
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1409-L1413

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowUniverseQuery_order (P : TannerSquarePresentation) (I : StateRows P)
    {r : ℝ} (hr : 0 ≤ r) : (rowUniverseQuery P I hr).1=
      (Finset.univ : Finset (Event P (statePoints I) r)).sort (eventPriorityLE P (statePoints I) r) := by sorry
