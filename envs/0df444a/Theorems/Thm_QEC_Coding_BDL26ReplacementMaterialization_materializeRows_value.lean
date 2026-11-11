-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_materializeRows_value
-- name    : QEC.Coding.BDL26ReplacementMaterialization.materializeRows_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T03:44:46.807461+00:00
-- url     : https://prove2.me/theorems/939a3288-74ef-41e0-b6ab-5bad2f1b0de5
-- title:
--   BDL26 Replacement Materialization: materialize Rows value
-- statement:
--   The BDL26 Replacement Materialization construction uses the materialize Rows value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L456-L467
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L456-L467

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ReplacementMaterialization
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26ReplacementMaterialization.materializeRows_value {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (materializeRows p n (emittedRows p n J T)).1 =
      (vertexInputList (StagePresentation p (n+1))).map (fun v => (v,physicalSuccessorOutput p n J T v)) := by sorry
