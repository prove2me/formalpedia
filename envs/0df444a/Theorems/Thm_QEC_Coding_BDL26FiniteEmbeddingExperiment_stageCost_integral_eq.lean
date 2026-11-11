-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_integral_eq
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.stageCost_integral_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:33:11.194959+00:00
-- url     : https://prove2.me/theorems/b9cff94f-c228-424c-a6bf-218cbfee7bb6
-- title:
--   BDL26 Finite Embedding Experiment: stage Cost integral eq
-- statement:
--   Exact random-input law and Tonelli identity, with no independent-output claim.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L162-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L162-L172

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.stageCost_integral_eq {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (∫⁻ z, stageCost p n i z ∂experimentLaw p n) =
      ∫⁻ J, ∫⁻ T, jointStageCost p i.val (J,T)
        ∂physicalTableLaw p i.val ∂outputLaw p i.val := by sorry
