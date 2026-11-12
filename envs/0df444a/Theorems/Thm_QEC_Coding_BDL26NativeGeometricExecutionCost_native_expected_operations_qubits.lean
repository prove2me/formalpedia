-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecutionCost_native_expected_operations_qubits
-- name    : QEC.Coding.BDL26NativeGeometricExecutionCost.native_expected_operations_qubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:59:05.925015+00:00
-- url     : https://prove2.me/theorems/3ef5a089-84b5-4645-b456-aebf4d8c92d3
-- title:
--   BDL26 Native Geometric Execution Cost: native expected operations qubits
-- statement:
--   Finite expected TOTAL paid native primitive operations in actual qubits.
--   The coefficient depends only on p; S, n, J and the random table do not occur in
--   it. This remains an internal single-perturbation theorem, not recursive output
--   independence or the public recursive embedding bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecutionCost.lean#L1018-L1026
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecutionCost.lean#L1018-L1026

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricScanCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_StrictSlackMoments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricExecutionCost
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem QEC.Coding.BDL26NativeGeometricExecutionCost.native_expected_operations_qubits (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    (∫⁻ T, nativeOperationCost S n J (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) T ∂nativeTableMeasure S n p) ≤
        (nativeOperationCoefficient ((6*p.m+2)*p.lambda) (dependencyBound p.M)*
          (Fintype.card (Presentation S n).Q+1)^nativeOperationDegree : ℕ) := by sorry
