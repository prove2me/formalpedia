-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_common_paid_geometry_ae
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.common_paid_geometry_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:29:54.015055+00:00
-- url     : https://prove2.me/theorems/5d6db3e0-02ba-40ac-885f-ed7bc9f1945f
-- title:
--   BDL26 Countable Embedding Experiment: common paid geometry ae
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the common paid geometry ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L278-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L278-L285

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

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.common_paid_geometry_ae {L : ℝ} (p : GeometricParameters L) :
    ∀ᵐ omega ∂streamLaw p, omega ∈ allFiniteSuccess p ∧
      (∀ i, streamHalts p i omega) ∧
      (∀ N, prefixStageCost p N omega < ∞) ∧
      (∀ n, PhysicalSuccessorFacts p n (levelMap p omega n) (omega n)) ∧
      ∀ n, PhysicalGeometry (perturbationOddScale p) n (levelMap p omega n) p.t := by sorry
