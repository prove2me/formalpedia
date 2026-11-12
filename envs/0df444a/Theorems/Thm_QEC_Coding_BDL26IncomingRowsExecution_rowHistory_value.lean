-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowHistory_value
-- name    : QEC.Coding.BDL26IncomingRowsExecution.rowHistory_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:27:02.427277+00:00
-- url     : https://prove2.me/theorems/f25b373e-f749-4355-95fa-4333c36a6aeb
-- title:
--   BDL26 Incoming Rows Execution: row History value
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the row History value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1202-L1205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1202-L1205

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

theorem QEC.Coding.BDL26IncomingRowsExecution.rowHistory_value {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : rowHistory p N z=history p N z := by sorry
