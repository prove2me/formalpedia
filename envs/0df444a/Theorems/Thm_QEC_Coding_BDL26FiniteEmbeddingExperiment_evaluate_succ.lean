-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_evaluate_succ
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.evaluate_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:00:19.366214+00:00
-- url     : https://prove2.me/theorems/f45b98eb-564b-4000-b203-43f307087c22
-- title:
--   BDL26 Finite Embedding Experiment: evaluate succ
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the evaluate succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Core.lean#L123-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Core.lean#L123-L125

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.evaluate_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p (n+1)) :
    evaluate p (n+1) z = physicalSuccessorOutput p n (evaluate p n z.1) z.2 := by sorry

attribute [defeq] QEC.Coding.BDL26FiniteEmbeddingExperiment.evaluate_succ
