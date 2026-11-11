-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_jointRowStageCost_le
-- name    : QEC.Coding.BDL26IncomingRowsExecution.jointRowStageCost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:25:46.940197+00:00
-- url     : https://prove2.me/theorems/d10ddb70-ad9e-4935-9005-550b30af3970
-- title:
--   BDL26 Incoming Rows Execution: joint Row Stage Cost le
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the joint Row Stage Cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1264-L1269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1264-L1269

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

theorem QEC.Coding.BDL26IncomingRowsExecution.jointRowStageCost_le {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (w : StageMaps p n × StageTables p n) : jointRowStageCost p n w ≤
      ((6*Fintype.card (Vertex (StagePresentation p n))+1 : ℕ) : ℝ≥0∞)*jointStageCost p n w := by sorry
