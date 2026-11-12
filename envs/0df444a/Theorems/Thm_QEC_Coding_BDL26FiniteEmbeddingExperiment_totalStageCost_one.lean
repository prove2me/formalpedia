-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_totalStageCost_one
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.totalStageCost_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:49:42.286868+00:00
-- url     : https://prove2.me/theorems/21350dc6-83bf-4070-8bf0-991228c0be4a
-- title:
--   BDL26 Finite Embedding Experiment: total Stage Cost one
-- statement:
--   The single actual stage starts at the literal seed, including on exceptional tables.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L92-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L92-L96

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26QuantitativeBounds
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.totalStageCost_one {L : ℝ} (p : GeometricParameters L)
    (z : Experiment p 1) :
    totalStageCost p 1 z = jointStageCost p 0
      (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p), z.2) := by sorry
