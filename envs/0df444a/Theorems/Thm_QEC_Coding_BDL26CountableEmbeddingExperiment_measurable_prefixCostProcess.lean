-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_prefixCostProcess
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_prefixCostProcess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:26:17.710414+00:00
-- url     : https://prove2.me/theorems/bc67e11c-e62c-4359-9d83-72bbd66f28bb
-- title:
--   BDL26 Countable Embedding Experiment: measurable prefix Cost Process
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the measurable prefix Cost Process property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L161-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L161-L163

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.measurable_prefixCostProcess {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : Omega p => fun N => prefixStageCost p N omega) := by sorry
