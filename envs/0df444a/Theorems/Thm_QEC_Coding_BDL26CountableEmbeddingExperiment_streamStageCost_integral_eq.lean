-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_integral_eq
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_integral_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:29:33.696962+00:00
-- url     : https://prove2.me/theorems/1168013d-77ba-4ee9-82c9-23a1825aadb6
-- title:
--   BDL26 Countable Embedding Experiment: stream Stage Cost integral eq
-- statement:
--   Incoming geometry can depend on earlier noise; only the current table is fresh.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L211-L221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L211-L221

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_integral_eq {L : ℝ} (p : GeometricParameters L) (i : ℕ) :
    (∫⁻ omega, streamStageCost p i omega ∂streamLaw p) =
      ∫⁻ J, ∫⁻ T, jointStageCost p i (J,T) ∂physicalTableLaw p i ∂outputLaw p i := by sorry
