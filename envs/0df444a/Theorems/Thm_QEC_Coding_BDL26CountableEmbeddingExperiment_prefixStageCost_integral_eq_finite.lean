-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_integral_eq_finite
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_integral_eq_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:53:07.6532+00:00
-- url     : https://prove2.me/theorems/96ec0699-e49f-47e9-9b5e-f7d7ef74ab12
-- title:
--   BDL26 Countable Embedding Experiment: prefix Stage Cost integral eq finite
-- statement:
--   Exact transport of the original total-cost integral, including exceptional inputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L230-L239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L230-L239

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_integral_eq_finite {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ omega, prefixStageCost p N omega ∂streamLaw p) =
      ∫⁻ z, totalStageCost p N z ∂experimentLaw p N := by sorry
