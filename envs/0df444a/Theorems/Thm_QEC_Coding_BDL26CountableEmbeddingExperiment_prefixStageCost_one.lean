-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_one
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:23:03.897963+00:00
-- url     : https://prove2.me/theorems/9f5819e6-1d01-48df-8953-ccb8c74ea832
-- title:
--   BDL26 Countable Embedding Experiment: prefix Stage Cost one
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the prefix Stage Cost one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L61-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L61-L65

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_one {L : ℝ} (p : GeometricParameters L) (omega : Omega p) :
    prefixStageCost p 1 omega = jointStageCost p 0
      (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p), omega 0) := by sorry
