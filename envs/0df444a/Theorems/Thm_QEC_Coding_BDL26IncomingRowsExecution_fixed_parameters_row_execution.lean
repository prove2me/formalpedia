-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_fixed_parameters_row_execution
-- name    : QEC.Coding.BDL26IncomingRowsExecution.fixed_parameters_row_execution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T07:15:03.25358+00:00
-- url     : https://prove2.me/theorems/daa62069-1876-4ac0-857f-0ea59a276e14
-- title:
--   BDL26 Incoming Rows Execution: fixed parameters row execution
-- statement:
--   Parameters are fixed before every prefix and every random input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1380-L1389
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L1380-L1389

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26IncomingRowsExecution
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] BDL26RandomPerturbation.countedLabelListMeasurable
  BDL26RandomPerturbation.countedLabelListSingleton

theorem QEC.Coding.BDL26IncomingRowsExecution.fixed_parameters_row_execution (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N,
      Measurable (rowTotalCost p N) ∧
      (∫⁻ z, rowTotalCost p N z ∂experimentLaw p N) ≤
        (((391*operationConstant ((6*p.m+2)*p.lambda)*65^10)*(stageQubits p N+1)^12 : ℕ) : ℝ≥0∞) ∧
      ∀ᵐ z ∂experimentLaw p N, z ∈ finiteSuccess p N ∧ rowTotalCost p N z<∞ := by sorry
