-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_successorCode_value
-- name    : QEC.Coding.BDL26ReplacementMaterialization.successorCode_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T03:43:45.144198+00:00
-- url     : https://prove2.me/theorems/8b88f795-6c73-42cf-bd68-1e4ccd0c28e1
-- title:
--   BDL26 Replacement Materialization: successor Code value
-- statement:
--   The BDL26 Replacement Materialization construction uses the successor Code value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L395-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L395-L406

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

theorem QEC.Coding.BDL26ReplacementMaterialization.successorCode_value {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (v : Vertex (StagePresentation p (n+1))) :
    (successorCode p n v).eval J =
      replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n) J v := by sorry
