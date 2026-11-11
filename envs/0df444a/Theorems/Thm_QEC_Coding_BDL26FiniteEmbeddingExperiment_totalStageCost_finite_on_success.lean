-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_totalStageCost_finite_on_success
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.totalStageCost_finite_on_success
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:27:38.175569+00:00
-- url     : https://prove2.me/theorems/dea53bc0-815a-44c7-83f8-a07946396e3d
-- title:
--   BDL26 Finite Embedding Experiment: total Stage Cost finite on success
-- statement:
--   Finiteness holds on exactly the existing simultaneous Halts-and-Good event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L237-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L237-L241

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.totalStageCost_finite_on_success {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p n) (h : z ∈ finiteSuccess p n) : totalStageCost p n z < ∞ := by sorry
