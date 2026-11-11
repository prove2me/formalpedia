-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_materializeRows_labels
-- name    : QEC.Coding.BDL26ReplacementMaterialization.materializeRows_labels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:44:11.270965+00:00
-- url     : https://prove2.me/theorems/61b05690-4a68-49c3-83f3-8720cfd2e319
-- title:
--   BDL26 Replacement Materialization: materialize Rows labels
-- statement:
--   The BDL26 Replacement Materialization construction uses the materialize Rows labels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L469-L472
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L469-L472

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

theorem QEC.Coding.BDL26ReplacementMaterialization.materializeRows_labels {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (R : List (Vertex (StagePresentation p n) × Space)) :
    ((materializeRows p n R).1).map Prod.fst = vertexInputList (StagePresentation p (n+1)) := by sorry
