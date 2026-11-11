-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowTotalCost_le_scaled
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowTotalCost_le_scaled
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:27:51.341414+00:00
-- url     : https://prove2.me/theorems/4a03ecb1-1c39-4064-ae7d-c47819e0a100
-- title:
--   BDL26 Incoming Rows Execution: row Total Cost le scaled
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Total Cost le scaled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1339-L1348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1339-L1348

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowTotalCost_le_scaled {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : rowTotalCost p N z ≤
      ((391*(stageQubits p N+1) : ℕ) : ℝ≥0∞)*totalStageCost p N z := by sorry
