-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecutionCost_native_expected_steps_sq
-- name    : QEC.Coding.BDL26NativeGeometricExecutionCost.native_expected_steps_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:54:13.26152+00:00
-- url     : https://prove2.me/theorems/e25ae5a4-0aba-4e65-8c2e-d6b1c500a160
-- title:
--   BDL26 Native Geometric Execution Cost: native expected steps sq
-- statement:
--   Strict slack is proved for the actual keyed supports and original product
--   law before the merged second-moment theorem is applied.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecutionCost.lean#L360-L413
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecutionCost.lean#L360-L413

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

theorem QEC.Coding.BDL26NativeGeometricExecutionCost.native_expected_steps_sq (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    (∫⁻ T, (nativeTotalSteps S n J (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) T)^2 ∂nativeTableMeasure S n p) ≤
        (2*(Fintype.card (Triangle (Presentation S n)))^8*
          (dependencyBound p.M+2)^2 : ℕ) := by sorry
