-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_le_prefix
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_le_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:52:52.566829+00:00
-- url     : https://prove2.me/theorems/e62d9dad-7534-43f7-9f06-ece9a37272bd
-- title:
--   BDL26 Countable Embedding Experiment: stream Stage Cost le prefix
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the stream Stage Cost le prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L105-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L105-L110

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_le_prefix {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (omega : Omega p) : streamStageCost p i.val omega ≤ prefixStageCost p N omega := by sorry
