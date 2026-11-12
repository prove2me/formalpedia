-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_nonhalting_default_and_cost
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.nonhalting_default_and_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:25:28.232313+00:00
-- url     : https://prove2.me/theorems/104255a2-5f95-4d1a-be3a-9b6fa1fd91dc
-- title:
--   BDL26 Countable Embedding Experiment: nonhalting default and cost
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the nonhalting default and cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L143-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L143-L146

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.nonhalting_default_and_cost {L : ℝ} (p : GeometricParameters L) (i : ℕ)
    (omega : Omega p) (h : ¬ streamHalts p i omega) :
    streamHaltTime p i omega = 0 ∧ streamStageCost p i omega = ∞ := by sorry
