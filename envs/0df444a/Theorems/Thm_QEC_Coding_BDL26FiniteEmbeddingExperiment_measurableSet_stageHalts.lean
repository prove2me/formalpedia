-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurableSet_stageHalts
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.measurableSet_stageHalts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:18:51.164863+00:00
-- url     : https://prove2.me/theorems/1fc480e8-fcce-4023-b37d-8da7b705b705
-- title:
--   BDL26 Finite Embedding Experiment: measurable Set stage Halts
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the measurable Set stage Halts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L162-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L162-L171

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.measurableSet_stageHalts {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) : MeasurableSet {z | stageHalts p n i z} := by sorry
