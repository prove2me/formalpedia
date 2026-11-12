-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stage_size_sum_le
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.stage_size_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:32:37.271138+00:00
-- url     : https://prove2.me/theorems/7c0c0331-5620-4024-a60a-7d9dfe4a34cd
-- title:
--   BDL26 Finite Embedding Experiment: stage size sum le
-- statement:
--   This arithmetic is applied to the derived single-stage expectation bounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L129-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L129-L145

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26QuantitativeBounds
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.stage_size_sum_le {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (∑ i : Fin n, (65 * stageQubits p i.val + 1)^10) ≤
      65^10 * (stageQubits p n + 1)^11 := by sorry
