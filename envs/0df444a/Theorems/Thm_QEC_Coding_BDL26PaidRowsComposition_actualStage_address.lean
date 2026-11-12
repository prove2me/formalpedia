-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_actualStage_address
-- name    : QEC.Coding.BDL26PaidRowsComposition.actualStage_address
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:35:54.813832+00:00
-- url     : https://prove2.me/theorems/1f7b23d1-f668-4ec2-9125-cf745ae71d90
-- title:
--   BDL26 Paid Rows Composition: actual Stage address
-- statement:
--   The BDL26 Paid Rows Composition construction uses the actual Stage address property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L388-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L388-L393

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26PaidRowsComposition.actualStage_address {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) (v : Vertex (StagePresentation p i.val)) :
    (v,actualStageCounters p N i time z v) = (v,stageCounters p N i time z v) ∧
      actualStageSamples p N i time z v = (tableAt p N i z) (v,actualStageCounters p N i time z v) := by sorry
