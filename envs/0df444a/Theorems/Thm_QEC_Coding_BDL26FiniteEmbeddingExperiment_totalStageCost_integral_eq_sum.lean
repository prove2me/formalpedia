-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_totalStageCost_integral_eq_sum
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.totalStageCost_integral_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:34:24.542578+00:00
-- url     : https://prove2.me/theorems/a79f4256-969c-42b2-9a6e-0ad0d662bb0f
-- title:
--   BDL26 Finite Embedding Experiment: total Stage Cost integral eq sum
-- statement:
--   Finite additivity needs measurability, rather than independence of the costs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L198-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L198-L201

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.totalStageCost_integral_eq_sum {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (∫⁻ z, totalStageCost p n z ∂experimentLaw p n) =
      ∑ i : Fin n, ∫⁻ z, stageCost p n i z ∂experimentLaw p n := by sorry
