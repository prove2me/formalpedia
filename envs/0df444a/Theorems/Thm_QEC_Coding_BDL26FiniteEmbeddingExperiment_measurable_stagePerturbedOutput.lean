-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePerturbedOutput
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_stagePerturbedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:25:34.665687+00:00
-- url     : https://prove2.me/theorems/3a6ffc5e-586a-4178-b48e-decb29a9f774
-- title:
--   BDL26 Finite Embedding Experiment: measurable stage Perturbed Output
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the measurable stage Perturbed Output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L194-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L194-L201

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_stagePerturbedOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) : Measurable (stagePerturbedOutput p n i) := by sorry
