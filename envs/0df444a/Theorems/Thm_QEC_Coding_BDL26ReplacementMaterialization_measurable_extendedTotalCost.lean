-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_measurable_extendedTotalCost
-- name    : QEC.Coding.BDL26ReplacementMaterialization.measurable_extendedTotalCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:13:39.746435+00:00
-- url     : https://prove2.me/theorems/3f671a99-6782-410f-92cf-d58e0022d177
-- title:
--   BDL26 Replacement Materialization: measurable extended Total Cost
-- statement:
--   The BDL26 Replacement Materialization construction uses the measurable extended Total Cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L618-L625
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L618-L625

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

theorem QEC.Coding.BDL26ReplacementMaterialization.measurable_extendedTotalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (extendedTotalCost p N) := by sorry
