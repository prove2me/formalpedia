-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_paid_source_even
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_paid_source_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:29:47.497359+00:00
-- url     : https://prove2.me/theorems/e3d90b31-fac9-45ac-8d47-dff6a075693e
-- title:
--   BDL26 Countable Embedding Experiment: all Finite Success paid source even
-- statement:
--   All source-even levels, including the seed, share the same paid success event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L288-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L288-L292

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_paid_source_even {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (k : ℕ) :
    prefixStageCost p (2*k) omega < ∞ ∧
      PhysicalGeometry (perturbationOddScale p) (2*k) (levelMap p omega (2*k)) p.t := by sorry
