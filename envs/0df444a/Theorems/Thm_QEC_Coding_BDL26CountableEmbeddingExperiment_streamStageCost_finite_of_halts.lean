-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_finite_of_halts
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_finite_of_halts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:53:17.463202+00:00
-- url     : https://prove2.me/theorems/883bea2a-98d4-4f53-a819-1935fa586fc1
-- title:
--   BDL26 Countable Embedding Experiment: stream Stage Cost finite of halts
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the stream Stage Cost finite of halts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L89-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L89-L94

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_finite_of_halts {L : ℝ} (p : GeometricParameters L) (i : ℕ)
    (omega : Omega p) (h : streamHalts p i omega) : streamStageCost p i omega < ∞ := by sorry
