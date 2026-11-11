-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finite_stage_cost_parameters
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.finite_stage_cost_parameters
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:51:09.679809+00:00
-- url     : https://prove2.me/theorems/d537f623-f359-449b-abc1-0cc209390b9d
-- title:
--   BDL26 Finite Embedding Experiment: finite stage cost parameters
-- statement:
--   Numerical parameters are chosen before every finite depth. This is the
--   expected cost of the existing counted stages, not uniform constructor runtime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L250-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L250-L259

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.finite_stage_cost_parameters (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ n : ℕ,
      Measurable (totalStageCost p n) ∧
      (∫⁻ z, totalStageCost p n z ∂experimentLaw p n) ≤
        ((operationConstant ((6*p.m+2)*p.lambda) *
          (65^10 * (stageQubits p n+1)^11) : ℕ) : ℝ≥0∞) ∧
      ∀ᵐ z ∂experimentLaw p n, z ∈ finiteSuccess p n ∧ totalStageCost p n z < ∞ := by sorry
