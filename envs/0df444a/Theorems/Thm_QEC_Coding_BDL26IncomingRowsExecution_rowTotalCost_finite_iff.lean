-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowTotalCost_finite_iff
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowTotalCost_finite_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T03:53:40.884198+00:00
-- url     : https://prove2.me/theorems/d0b5ecea-39ba-401b-9ec3-57231e5951a1
-- title:
--   BDL26 Incoming Rows Execution: row Total Cost finite iff
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Total Cost finite iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1292-L1302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1292-L1302

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowTotalCost_finite_iff {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : rowTotalCost p N z<∞ ↔ ∀ i : Fin N, stageHalts p N i z := by sorry
