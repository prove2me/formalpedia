-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowStageCost_last
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowStageCost_last
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:26:26.501833+00:00
-- url     : https://prove2.me/theorems/32c91567-81f5-4407-b244-4214d69d5166
-- title:
--   BDL26 Incoming Rows Execution: row Stage Cost last
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row Stage Cost last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1249-L1252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1249-L1252

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowStageCost_last {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p (N+1)) :
    rowStageCost p (N+1) (Fin.last N) z=jointRowStageCost p N (evaluate p N z.1,z.2) := by sorry
