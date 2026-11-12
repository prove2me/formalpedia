-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_integral_le
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_integral_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T07:29:14.614903+00:00
-- url     : https://prove2.me/theorems/77478bb6-f263-45e7-837e-1b493409c4e1
-- title:
--   BDL26 Countable Embedding Experiment: stream Stage Cost integral le
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the stream Stage Cost integral le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L223-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L223-L227

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_integral_le {L : ℝ} (p : GeometricParameters L) (i : ℕ) :
    (∫⁻ omega, streamStageCost p i omega ∂streamLaw p) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) * (65*stageQubits p i+1)^10 : ℕ) : ℝ≥0∞) := by sorry
