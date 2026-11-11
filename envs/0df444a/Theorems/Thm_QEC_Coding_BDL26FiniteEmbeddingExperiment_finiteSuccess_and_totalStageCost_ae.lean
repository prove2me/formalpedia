-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_and_totalStageCost_ae
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.finiteSuccess_and_totalStageCost_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:35:55.233642+00:00
-- url     : https://prove2.me/theorems/048066d0-1db7-4b3f-9bf0-1143a554a87b
-- title:
--   BDL26 Finite Embedding Experiment: finite Success and total Stage Cost ae
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the finite Success and total Stage Cost ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L243-L246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L243-L246

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26QuantitativeBounds
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.finiteSuccess_and_totalStageCost_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    ∀ᵐ z ∂experimentLaw p n, z ∈ finiteSuccess p n ∧ totalStageCost p n z < ∞ := by sorry
