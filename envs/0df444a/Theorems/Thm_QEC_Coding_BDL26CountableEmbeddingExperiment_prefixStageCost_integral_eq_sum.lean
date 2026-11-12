-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_integral_eq_sum
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_integral_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:27:56.202615+00:00
-- url     : https://prove2.me/theorems/4af328be-d944-4f4e-bda5-6b02015649c3
-- title:
--   BDL26 Countable Embedding Experiment: prefix Stage Cost integral eq sum
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the prefix Stage Cost integral eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L241-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L241-L244

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_integral_eq_sum {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ omega, prefixStageCost p N omega ∂streamLaw p) =
      ∑ i : Fin N, ∫⁻ omega, streamStageCost p i.val omega ∂streamLaw p := by sorry
