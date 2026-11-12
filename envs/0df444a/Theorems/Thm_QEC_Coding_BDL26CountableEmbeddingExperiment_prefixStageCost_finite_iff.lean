-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_finite_iff
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_finite_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:52:56.577415+00:00
-- url     : https://prove2.me/theorems/ab09568a-bfd0-41a5-8e99-f0a240ddab25
-- title:
--   BDL26 Countable Embedding Experiment: prefix Stage Cost finite iff
-- statement:
--   No geometric success assumption is needed for this exact operational equivalence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L113-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L113-L123

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_finite_iff {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : Omega p) :
    prefixStageCost p N omega < ∞ ↔ ∀ i : Fin N, streamHalts p i.val omega := by sorry
