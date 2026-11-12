-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_all_prefixStageCost_finite_iff
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.all_prefixStageCost_finite_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:24:13.972805+00:00
-- url     : https://prove2.me/theorems/4e51e244-08a4-4ad3-90a2-319aea7485fb
-- title:
--   BDL26 Countable Embedding Experiment: all prefix Stage Cost finite iff
-- statement:
--   Simultaneous finite-prefix finiteness is exactly simultaneous stage termination.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L126-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L126-L133

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.all_prefixStageCost_finite_iff {L : ℝ} (p : GeometricParameters L)
    (omega : Omega p) :
    (∀ N, prefixStageCost p N omega < ∞) ↔ ∀ i, streamHalts p i omega := by sorry
