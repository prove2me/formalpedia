-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_original_execution_prefix
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.original_execution_prefix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:28:41.076826+00:00
-- url     : https://prove2.me/theorems/7e0f616e-2f55-4ce5-8232-fc3001759c42
-- title:
--   BDL26 Finite Embedding Experiment: original execution prefix
-- statement:
--   All original execution data, not just the final embedding, survive truncation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L97-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L97-L133

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.original_execution_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (i : Fin m) (time : ℕ) (z : Experiment p n) :
    stageCounters p m i time (experimentPrefix p m n h z) = stageCounters p n (i.castLE h) time z ∧
    stageSelected p m i time (experimentPrefix p m n h z) = stageSelected p n (i.castLE h) time z ∧
    (stageHalts p m i (experimentPrefix p m n h z) ↔ stageHalts p n (i.castLE h) z) ∧
    stageHaltTime p m i (experimentPrefix p m n h z) = stageHaltTime p n (i.castLE h) z ∧
    stageGeometricOutput p m i (experimentPrefix p m n h z) = stageGeometricOutput p n (i.castLE h) z ∧
    stagePerturbedOutput p m i (experimentPrefix p m n h z) = stagePerturbedOutput p n (i.castLE h) z ∧
    stagePhysicalOutput p m i (experimentPrefix p m n h z) = stagePhysicalOutput p n (i.castLE h) z := by sorry
