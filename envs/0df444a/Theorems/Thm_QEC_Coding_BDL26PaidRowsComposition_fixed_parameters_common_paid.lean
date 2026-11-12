-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_fixed_parameters_common_paid
-- name    : QEC.Coding.BDL26PaidRowsComposition.fixed_parameters_common_paid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T07:41:05.205465+00:00
-- url     : https://prove2.me/theorems/21d03472-f473-40c5-9e96-a4fe2dac8234
-- title:
--   BDL26 Paid Rows Composition: fixed parameters common paid
-- statement:
--   p is fixed before all prefix lengths and every point of the original stream.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L823-L840
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L823-L840

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26PaidRowsComposition.fixed_parameters_common_paid (L : ℝ) :
    ∃ p : GeometricParameters L,
      (∀ N, Measurable (streamObservation p N) ∧
        (∫⁻ omega, streamTotalCost p N omega ∂BDL26CountableEmbeddingExperiment.streamLaw p) ≤
          (((391*operationConstant ((6*p.m+2)*p.lambda)*65^10+65536*65^2+195)*
            (stageQubits p N+1)^12 : ℕ) : ℝ≥0∞)) ∧
      MeasurableSet (BDL26CountableEmbeddingExperiment.allFiniteSuccess p) ∧
      BDL26CountableEmbeddingExperiment.streamLaw p (BDL26CountableEmbeddingExperiment.allFiniteSuccess p) = 1 ∧
      ∀ᵐ omega ∂BDL26CountableEmbeddingExperiment.streamLaw p,
        omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p ∧
        (∀ N, streamTotalCost p N omega < ∞) ∧
        (∀ n, PhysicalSuccessorFacts p n (BDL26CountableEmbeddingExperiment.levelMap p omega n) (omega n)) ∧
        ∀ n, PhysicalGeometry (perturbationOddScale p) n
          (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t := by sorry
