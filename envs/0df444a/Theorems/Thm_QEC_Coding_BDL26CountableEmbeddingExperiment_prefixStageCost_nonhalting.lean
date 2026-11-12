-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_nonhalting
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_nonhalting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:25:42.130031+00:00
-- url     : https://prove2.me/theorems/fb2dea81-9d93-4421-9214-e1b135eb2135
-- title:
--   BDL26 Countable Embedding Experiment: prefix Stage Cost nonhalting
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the prefix Stage Cost nonhalting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L135-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L135-L141

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_nonhalting {L : ℝ} (p : GeometricParameters L) {i N : ℕ}
    (hi : i < N) (omega : Omega p) (h : ¬ streamHalts p i omega) :
    prefixStageCost p N omega = ∞ := by sorry
