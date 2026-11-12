-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_mono
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:23:22.044713+00:00
-- url     : https://prove2.me/theorems/7c0b0165-e270-47e5-87eb-b3b57fe31999
-- title:
--   BDL26 Countable Embedding Experiment: prefix Stage Cost mono
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the prefix Stage Cost mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L67-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L67-L72

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_mono {L : ℝ} (p : GeometricParameters L) (omega : Omega p) :
    Monotone (fun N => prefixStageCost p N omega) := by sorry
