-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_jointStageCost_integral_le
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.jointStageCost_integral_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:22:34.339194+00:00
-- url     : https://prove2.me/theorems/dd87d516-b44a-42b3-926c-f0bf110503e9
-- title:
--   BDL26 Finite Embedding Experiment: joint Stage Cost integral le
-- statement:
--   The input-good condition is derived from the literal seed recursion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L175-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L175-L189

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.jointStageCost_integral_le {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (∫⁻ J, ∫⁻ T, jointStageCost p n (J,T) ∂physicalTableLaw p n ∂outputLaw p n) ≤
      ((operationConstant ((6*p.m+2)*p.lambda) * (65*stageQubits p n+1)^10 : ℕ) : ℝ≥0∞) := by sorry
