-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamPaidObservation_law
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.streamPaidObservation_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:27:27.163268+00:00
-- url     : https://prove2.me/theorems/fd225776-3d44-4126-98ac-2eb2cd7e7e3c
-- title:
--   BDL26 Countable Embedding Experiment: stream Paid Observation law
-- statement:
--   This identifies the cost/history copula, rather than only their scalar marginals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L202-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L202-L208

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.streamPaidObservation_law {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (streamLaw p).map (streamPaidObservation p N) =
      (experimentLaw p N).map (finitePaidObservation p N) := by sorry
