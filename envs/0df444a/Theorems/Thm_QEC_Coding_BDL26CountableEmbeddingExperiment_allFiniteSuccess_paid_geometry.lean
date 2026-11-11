-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_paid_geometry
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_paid_geometry
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:28:53.834035+00:00
-- url     : https://prove2.me/theorems/18372813-7d2e-47be-8300-7472353d31a0
-- title:
--   BDL26 Countable Embedding Experiment: all Finite Success paid geometry
-- statement:
--   Operational and physical conclusions concern one and the same stream point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L269-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L269-L276

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_paid_geometry {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) :
    (∀ i, streamHalts p i omega) ∧
    (∀ N, prefixStageCost p N omega < ∞) ∧
    (∀ n, PhysicalSuccessorFacts p n (levelMap p omega n) (omega n)) ∧
    ∀ n, PhysicalGeometry (perturbationOddScale p) n (levelMap p omega n) p.t := by sorry
