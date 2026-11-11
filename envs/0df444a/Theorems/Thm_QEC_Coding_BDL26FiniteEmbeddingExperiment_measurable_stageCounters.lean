-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stageCounters
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_stageCounters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:18:57.852266+00:00
-- url     : https://prove2.me/theorems/761eaaab-c079-44bb-8851-a78cf0e70aff
-- title:
--   BDL26 Finite Embedding Experiment: measurable stage Counters
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the measurable stage Counters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L135-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L135-L146

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_stageCounters {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (time : ℕ) : Measurable (stageCounters p n i time) := by sorry
