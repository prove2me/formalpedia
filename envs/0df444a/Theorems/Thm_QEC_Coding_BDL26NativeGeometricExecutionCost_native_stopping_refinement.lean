-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecutionCost_native_stopping_refinement
-- name    : QEC.Coding.BDL26NativeGeometricExecutionCost.native_stopping_refinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:51:51.723534+00:00
-- url     : https://prove2.me/theorems/1e5c97a0-584d-4a44-9299-67b5a9c4c2ac
-- title:
--   BDL26 Native Geometric Execution Cost: native stopping refinement
-- statement:
--   The finite-fuel program returns precisely the first no-event state and
--   generated trace. Its exact numeric cost includes the terminal scan and emitter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecutionCost.lean#L286-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecutionCost.lean#L286-L316

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

theorem QEC.Coding.BDL26NativeGeometricExecutionCost.native_stopping_refinement (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n)
    (h : NativeHalts S n J hr lambda K T) :
    let m := nativeHaltTime S n J hr lambda K T
    (stopQ S n J hr lambda K T (m+1)).value =
      ⟨(prefixQ S n J hr lambda K T m).value,
        some (BDL26NativeStateRows.emitQ
          (prefixQ S n J hr lambda K T m).value.rows).value⟩ ∧
    (stopQ S n J hr lambda K T (m+1)).operations =
      (prefixQ S n J hr lambda K T m).operations+
        (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).2+
        5*SR.count S n+3 := by sorry
