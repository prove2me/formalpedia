-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamPaidObservation_original
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.streamPaidObservation_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:30:06.524283+00:00
-- url     : https://prove2.me/theorems/49e4a54d-af88-4c9c-8cd0-45d7e4256c2b
-- title:
--   BDL26 Countable Embedding Experiment: stream Paid Observation original
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the stream Paid Observation original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L178-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L178-L187

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.streamPaidObservation_original {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : Omega p) :
    streamPaidObservation p N omega = finitePaidObservation p N (truncate p N omega) := by sorry
