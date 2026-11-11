-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_eq_stageCost
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_eq_stageCost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T03:09:27.115223+00:00
-- url     : https://prove2.me/theorems/4c11a739-5176-4a07-998a-1ebb0c275c42
-- title:
--   BDL26 Countable Embedding Experiment: stream Stage Cost eq stage Cost
-- statement:
--   Numeric costs agree at every point, without a halting or good-input premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L42-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L42-L45

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_eq_stageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (omega : Omega p) :
    streamStageCost p i.val omega = stageCost p N i (truncate p N omega) := by sorry
