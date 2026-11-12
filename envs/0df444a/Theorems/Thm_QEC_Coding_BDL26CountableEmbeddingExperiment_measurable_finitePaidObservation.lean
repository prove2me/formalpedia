-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_finitePaidObservation
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_finitePaidObservation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:29:14.233609+00:00
-- url     : https://prove2.me/theorems/fdb40dbe-e7af-4be2-8758-ed221fbcc6ad
-- title:
--   BDL26 Countable Embedding Experiment: measurable finite Paid Observation
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the measurable finite Paid Observation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L189-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L189-L193

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_finitePaidObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (finitePaidObservation p N) := by sorry
