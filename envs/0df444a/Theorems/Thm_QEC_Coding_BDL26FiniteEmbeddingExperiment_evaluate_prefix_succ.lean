-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_evaluate_prefix_succ
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.evaluate_prefix_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:03:15.608052+00:00
-- url     : https://prove2.me/theorems/126d440f-5930-4c5a-a67d-5cef214145b5
-- title:
--   BDL26 Finite Embedding Experiment: evaluate prefix succ
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the evaluate prefix succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Core.lean#L139-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Core.lean#L139-L147

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.evaluate_prefix_succ {L : ℝ} (p : GeometricParameters L) {i n : ℕ}
    (hi : i < n) (z : Experiment p n) :
    evaluate p (i+1) (experimentPrefix p (i+1) n hi z) =
      physicalSuccessorOutput p i (stageInput p n ⟨i,hi⟩ z) (tableAt p n ⟨i,hi⟩ z) := by sorry
