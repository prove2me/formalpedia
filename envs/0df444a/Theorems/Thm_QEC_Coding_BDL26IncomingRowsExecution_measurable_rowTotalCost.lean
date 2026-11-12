-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_measurable_rowTotalCost
-- name    : QEC.Coding.BDL26IncomingRowsExecution.measurable_rowTotalCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:50:22.989721+00:00
-- url     : https://prove2.me/theorems/15ebd652-32a1-47d8-894f-4b48288d9a93
-- title:
--   BDL26 Incoming Rows Execution: measurable row Total Cost
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the measurable row Total Cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1228-L1230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1228-L1230

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

theorem QEC.Coding.BDL26IncomingRowsExecution.measurable_rowTotalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (rowTotalCost p N) := by sorry
