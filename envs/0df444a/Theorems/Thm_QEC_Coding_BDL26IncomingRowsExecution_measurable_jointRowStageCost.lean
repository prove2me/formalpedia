-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_measurable_jointRowStageCost
-- name    : QEC.Coding.BDL26IncomingRowsExecution.measurable_jointRowStageCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:27:26.162+00:00
-- url     : https://prove2.me/theorems/e6bdc6bc-a992-4c16-ac80-72eddd5dfabd
-- title:
--   BDL26 Incoming Rows Execution: measurable joint Row Stage Cost
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the measurable joint Row Stage Cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1219-L1222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1219-L1222

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

theorem QEC.Coding.BDL26IncomingRowsExecution.measurable_jointRowStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (jointRowStageCost p n) := by sorry
