-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_totalStageCost_integral_le_sum
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.totalStageCost_integral_le_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:27:15.196202+00:00
-- url     : https://prove2.me/theorems/b5d092e5-7bd0-4d94-91ed-b3aad02052de
-- title:
--   BDL26 Finite Embedding Experiment: total Stage Cost integral le sum
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the total Stage Cost integral le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L203-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L203-L212

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.totalStageCost_integral_le_sum {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (∫⁻ z, totalStageCost p n z ∂experimentLaw p n) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) *
        ∑ i : Fin n, (65*stageQubits p i.val+1)^10 : ℕ) : ℝ≥0∞) := by sorry
