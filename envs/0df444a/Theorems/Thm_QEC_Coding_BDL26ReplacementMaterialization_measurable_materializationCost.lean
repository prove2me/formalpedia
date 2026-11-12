-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_measurable_materializationCost
-- name    : QEC.Coding.BDL26ReplacementMaterialization.measurable_materializationCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:48:05.31022+00:00
-- url     : https://prove2.me/theorems/779628ee-d3c8-46b2-ae1c-10a33a673518
-- title:
--   BDL26 Replacement Materialization: measurable materialization Cost
-- statement:
--   The BDL26 Replacement Materialization construction uses the measurable materialization Cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L530-L535
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L530-L535

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

theorem QEC.Coding.BDL26ReplacementMaterialization.measurable_materializationCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (materializationCost p n) := by sorry
