-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedTotalCost_eq
-- name    : QEC.Coding.BDL26ReplacementMaterialization.extendedTotalCost_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:11:07.008551+00:00
-- url     : https://prove2.me/theorems/3289fb58-2f1b-4813-8473-3461b302606f
-- title:
--   BDL26 Replacement Materialization: extended Total Cost eq
-- statement:
--   The BDL26 Replacement Materialization construction uses the extended Total Cost eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L585-L589
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L585-L589

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

theorem QEC.Coding.BDL26ReplacementMaterialization.extendedTotalCost_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) :
    extendedTotalCost p N z = totalStageCost p N z + (totalMaterializationCost p N z : ℕ) := by sorry
