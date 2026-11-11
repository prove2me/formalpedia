-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_evaluate
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_evaluate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:00:51.86427+00:00
-- url     : https://prove2.me/theorems/da504f44-a343-479b-9b60-56763848b5fa
-- title:
--   BDL26 Finite Embedding Experiment: measurable evaluate
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the measurable evaluate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Core.lean#L186-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Core.lean#L186-L206

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EmbeddingKernel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_evaluate {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (evaluate p n) := by sorry
