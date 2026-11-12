-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_original
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:22:07.958207+00:00
-- url     : https://prove2.me/theorems/2cc55466-707d-4f52-87f0-06bd86727765
-- title:
--   BDL26 Countable Embedding Experiment: stream Stage Cost original
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the stream Stage Cost original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L35-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L35-L39

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_original {L : ℝ} (p : GeometricParameters L) (i : ℕ)
    (omega : Omega p) :
    streamStageCost p i omega = actualExecutionCost (StagePresentation p i)
      (levelMap p omega i) (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) (omega i) := by sorry
