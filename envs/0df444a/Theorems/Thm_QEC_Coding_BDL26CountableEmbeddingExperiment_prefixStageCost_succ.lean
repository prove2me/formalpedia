-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_succ
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:51:57.634216+00:00
-- url     : https://prove2.me/theorems/05aaca12-4d9a-41c4-bfd7-43f50cc50e17
-- title:
--   BDL26 Countable Embedding Experiment: prefix Stage Cost succ
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the prefix Stage Cost succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L56-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L56-L59

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_succ {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : Omega p) :
    prefixStageCost p (N+1) omega = prefixStageCost p N omega + streamStageCost p N omega := by sorry
