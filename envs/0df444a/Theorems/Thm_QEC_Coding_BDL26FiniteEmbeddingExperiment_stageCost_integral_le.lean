-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_integral_le
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.stageCost_integral_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:25:17.50221+00:00
-- url     : https://prove2.me/theorems/97cc4586-7119-4c1b-b641-f5f32357be57
-- title:
--   BDL26 Finite Embedding Experiment: stage Cost integral le
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the stage Cost integral le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L191-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L191-L195

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.stageCost_integral_le {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (∫⁻ z, stageCost p n i z ∂experimentLaw p n) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) * (65*stageQubits p i.val+1)^10 : ℕ) : ℝ≥0∞) := by sorry
