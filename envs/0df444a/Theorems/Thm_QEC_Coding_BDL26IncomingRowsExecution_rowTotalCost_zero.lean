-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowTotalCost_zero
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowTotalCost_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:21:52.664823+00:00
-- url     : https://prove2.me/theorems/7d08fd4b-a9e9-4bac-ae27-b555157de9ac
-- title:
--   BDL26 Incoming Rows Execution: row Total Cost zero
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Total Cost zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1237-L1239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1237-L1239

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowTotalCost_zero {L : ℝ} (p : GeometricParameters L)
    (z : Experiment p 0) : rowTotalCost p 0 z=0 := by sorry
